"""Fixed checker for the Lean evidence. Agents never edit this file or the original outputs.

    python check.py GROUP [KEY ...]        # GROUP in identical, anchor, wrong_reason

For each KEY with a snippet evidence/GROUP/KEY.lean, the checker builds one file:
    namespace R  <rejected output, verbatim, imports removed>  end R
    namespace P  <partner or anchor output, verbatim>          end P      (identical and anchor only)
    <snippet>
and runs it on top of Mathlib. It records Lean errors and `#print axioms` of every certificate.
- identical / anchor: the snippet must define `theorem cert`. The checker verifies in Lean that the type of
  `cert` is, up to universe instantiation and definitional unfolding, (statement of R's main theorem) <->
  (statement of P's main theorem); that both directions are lambdas whose body uses the hypothesis; and
  that `cert` depends on no `sorryAx`.
- wrong_reason: every theorem in the snippet whose name starts with `claim` is a checked fact about the
  output's objects; the checker records that each compiles and depends on no `sorryAx`.
Results go to evidence/GROUP/KEY.check.json.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

from lean_repl import Repl

HERE = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

MATCH = r'''
open Lean Meta Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let local_ := env.constants.map₂.toList.map (·.1)
  let find (ns : Name) (s : String) : Option Name :=
    (local_.filter fun n => ns.isPrefixOf n && n.getRoot == ns && n.lastComponentAsString == s).getLast?
  let some rn := find `R "RTHM" | logInfo "@@MATCH missing R theorem"
  let some pn := find `P "PTHM" | logInfo "@@MATCH missing P theorem"
  let some cert := env.find? `cert | logInfo "@@MATCH missing cert"
  let r := (env.find? rn).get!
  let p := (env.find? pn).get!
  let ok ← liftTermElabM do
    let inst (ci : ConstantInfo) : MetaM Expr := do
      let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
      pure (ci.type.instantiateLevelParams ci.levelParams us)
    let ct ← inst cert
    let rt ← inst r
    let pt ← inst p
    withTransparency .default <| isDefEq ct (mkApp2 (mkConst ``Iff) rt pt)
  let v := cert.value?.getD (mkConst `none)
  let v ← liftTermElabM (instantiateMVars v)
  let uses : String :=
    if v.isAppOfArity ``Iff.intro 4 then
      let a := v.getArg! 2
      let b := v.getArg! 3
      if a.isLambda && b.isLambda then
        s!"{a.bindingBody!.hasLooseBVars && b.bindingBody!.hasLooseBVars}"
      else "shape-unknown"
    else "shape-unknown"
  logInfo m!"@@MATCH {ok}\n@@USES {uses}\n@@RN {rn}\n@@PN {pn}"
'''


def body(code: str) -> str:
    return "\n".join(l for l in code.splitlines() if not l.strip().startswith("import "))


def main_thm(code: str) -> str:
    return re.findall(r"^\s*(?:theorem|lemma)\s+([^\s(:{\[]+)", code, re.M)[-1].split(".")[-1].strip("«»")


def build(group: str, item: dict, snippet: str) -> tuple[str, list[str]]:
    parts = ["namespace R", body(item["lean"]), "end R"]
    if group != "wrong_reason":
        other = item["partner_lean"] if group == "identical" else item["anchor_lean"]
        parts += ["namespace P", body(other), "end P"]
    parts.append(snippet)
    names = re.findall(r"^\s*(?:theorem|lemma)\s+(claim[^\s(:{\[]*)", snippet, re.M) if group == "wrong_reason" else ["cert"]
    parts += [f"#print axioms {n}" for n in names]
    if group != "wrong_reason":
        parts.append(MATCH.replace("RTHM", main_thm(item["lean"])).replace("PTHM", main_thm(other)))
    return "\n".join(parts), names


def main() -> None:
    group, keys = sys.argv[1], sys.argv[2:]
    items = {d["key"]: d for d in json.loads((HERE / f"inputs_{group}.json").read_text())}
    keys = keys or list(items)
    repl = Repl()
    for key in keys:
        snip_path = HERE / "evidence" / group / f"{key.replace(':', '_')}.lean"
        if not snip_path.exists():
            print(f"{key}: no snippet")
            continue
        code, names = build(group, items[key], snip_path.read_text())
        res = repl.run(code)
        msgs = res.get("messages", [])
        errors = [m["data"][:400] for m in msgs if m["severity"] == "error"]
        infos = [m["data"] for m in msgs if m["severity"] == "info"]
        axioms = {}
        for n in names:
            txt = next((i for i in infos if f"'{n}'" in i and "axiom" in i), "")
            found = set(re.findall(r"[\w.]+", txt.split("axioms:")[-1])) if "axioms:" in txt else set()
            axioms[n] = {"text": txt[:300], "sorry": "sorryAx" in found, "extra": sorted(found - ALLOWED - {"sorryAx"})}
        match = next((i for i in infos if i.startswith("@@MATCH")), "")
        rec = {"key": key, "group": group, "errors": errors, "axioms": axioms, "match": match}
        ok_axioms = all(not a["sorry"] and not a["extra"] for a in axioms.values()) and bool(axioms)
        if group == "wrong_reason":
            rec["verified"] = not errors and ok_axioms
        else:
            rec["verified"] = (not errors and ok_axioms and "@@MATCH true" in match and "@@USES true" in match)
        (snip_path.with_suffix(".check.json")).write_text(json.dumps(rec, ensure_ascii=False, indent=1))
        print(f"{key}: verified={rec['verified']} errors={len(errors)} {match.replace(chr(10), ' ')} "
              f"{ {n: ('sorry' if a['sorry'] else a['extra'] or 'ok') for n, a in axioms.items()} }")
        for e in errors[:3]:
            print("   ERR", e[:300].replace("\n", " "))
    repl.close()


if __name__ == "__main__":
    main()
