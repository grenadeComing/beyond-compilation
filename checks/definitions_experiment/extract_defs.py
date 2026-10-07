"""Extract, by a fixed rule, the Mathlib definitions that each Lean output uses.

    python beyond_v3_227/new_models/definitions_experiment/extract_defs.py

For every item, the output's code (without its import lines) is elaborated in the REPL on top of `import Mathlib`.
A metaprogram collects the constants used by the types of all declarations of the output, and by the values of its
definitions. Rule: keep constants from Mathlib modules only (core Lean, Init and Std constants such as Eq, Nat or
HMul.hMul are dropped), in order of first use, at most MAX_CONSTS; for each, the signature, the docstring and, for
definitions, the value when short. The material is capped at MAX_CHARS; truncation is recorded.
"""

from __future__ import annotations

import json
import re
from pathlib import Path

from lean_repl import Repl

HERE = Path(__file__).resolve().parent
MAX_CONSTS, MAX_CHARS = 30, 6000
TYPE_CHARS, DOC_CHARS, VAL_CHARS = 300, 400, 300

META = r'''
open Lean Elab Command Meta in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut seen : NameSet := {}
  for (n, ci) in env.constants.map₂.toList do
    if n.isInternal then continue
    let mut cs := ci.type.getUsedConstants
    match ci with
    | .defnInfo d => cs := cs ++ d.value.getUsedConstants
    | _ => pure ()
    for c in cs do
      if seen.contains c then continue
      seen := seen.insert c
      let some idx := env.getModuleIdxFor? c | continue
      let some info := env.find? c | continue
      let modName := env.header.moduleNames[idx.toNat]!
      let ty ← liftTermElabM (Meta.ppExpr info.type)
      let doc ← findDocString? env c
      let kind := match info with
        | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor" | .axiomInfo _ => "axiom" | .opaqueInfo _ => "opaque"
        | .recInfo _ => "recursor" | .quotInfo _ => "quot"
      let val ← match info with
        | .defnInfo d => do
            let f ← liftTermElabM (Meta.ppExpr d.value)
            pure (toString f)
        | _ => pure ""
      logInfo m!"@@CONST {c}\n@@MOD {modName}\n@@KIND {kind}\n@@TYPE {ty}\n@@DOC {doc.getD ""}\n@@VAL {(val.take 2000)}"
'''

FIELD = re.compile(r"^@@(CONST|MOD|KIND|TYPE|DOC|VAL) ?", re.M)


def parse(msg: str) -> dict:
    parts = FIELD.split(msg)
    out, i = {}, 1
    while i + 1 < len(parts):
        out[parts[i]] = parts[i + 1].strip()
        i += 2
    return out


def cut(s: str, n: int) -> str:
    s = " ".join(s.split())
    return s if len(s) <= n else s[: n - 3] + "..."


def material(consts: list[dict]) -> tuple[str, bool, int]:
    kept = [c for c in consts if c.get("MOD", "").startswith("Mathlib")]
    truncated = len(kept) > MAX_CONSTS
    lines = []
    for c in kept[:MAX_CONSTS]:
        entry = f"- {c['CONST']} ({c['KIND']}) : {cut(c['TYPE'], TYPE_CHARS)}"
        if c.get("DOC"):
            entry += f"\n  doc: {cut(c['DOC'], DOC_CHARS)}"
        if c["KIND"] == "def" and c.get("VAL") and len(" ".join(c["VAL"].split())) <= VAL_CHARS:
            entry += f"\n  value: {cut(c['VAL'], VAL_CHARS)}"
        if sum(len(l) + 1 for l in lines) + len(entry) > MAX_CHARS:
            truncated = True
            break
        lines.append(entry)
    return "\n".join(lines), truncated, len(kept)


def main() -> None:
    items = [json.loads(l) for l in (HERE / "items.jsonl").read_text().splitlines()]
    out_path = HERE / "defs.jsonl"
    done = {json.loads(l)["key"] for l in out_path.read_text().splitlines()} if out_path.exists() else set()
    repl = Repl()
    with out_path.open("a", encoding="utf-8") as f:
        for it in items:
            if it["key"] in done:
                continue
            body = "\n".join(l for l in it["lean"].splitlines() if not l.strip().startswith("import "))
            try:
                res = repl.run(body + "\n" + META)
            except RuntimeError as e:
                f.write(json.dumps({"key": it["key"], "error": str(e)[:500]}) + "\n")
                repl = Repl()
                continue
            msgs = res.get("messages", [])
            consts = [parse(m["data"]) for m in msgs if m["severity"] == "info" and m["data"].startswith("@@CONST")]
            errors = [m["data"][:300] for m in msgs if m["severity"] == "error"]
            text, truncated, n_kept = material(consts)
            f.write(json.dumps({"key": it["key"], "n_constants": len(consts), "n_mathlib": n_kept, "truncated": truncated,
                                "lean_errors": errors, "material": text}, ensure_ascii=False) + "\n")
            f.flush()
            print(f"{it['key']}: {n_kept} Mathlib constants{' (truncated)' if truncated else ''}{' ERRORS' if errors else ''}", flush=True)
    repl.close()


if __name__ == "__main__":
    main()
