"""Re-run snippets with check.py's file layout (namespace R ... end R, namespace P ... end P, snippet)
and print ALL Lean messages, including `#print axioms` of auxiliary theorems (not_cert, cert_real,
claim_*) that check.py does not record. Also covers BC046, which check.py cannot process.

    cd lean_evidence && python3 evidence/anchor/run_extra.py > evidence/anchor/extra_run.log
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from check import body  # noqa: E402
from lean_repl import Repl  # noqa: E402

FILES = {
    "BC042:astra": "BC042_astra.lean",
    "BC046:opus": "BC046_opus.manual.lean",
    "BC092:astra": "BC092_astra.lean",
    "BC160:opus": "BC160_opus.lean",
    "BC180:opus": "BC180_opus.lean",
}
items = {d["key"]: d for d in json.loads((ROOT / "inputs_anchor.json").read_text())}
repl = Repl()
for key, fname in FILES.items():
    it = items[key]
    snippet = (Path(__file__).parent / fname).read_text()
    code = "\n".join(["namespace R", body(it["lean"]), "end R",
                      "namespace P", body(it["anchor_lean"]), "end P", snippet])
    res = repl.run(code)
    print("=====", key, fname)
    for m in res.get("messages", []):
        print(f"[{m['severity']} line {m.get('pos', {}).get('line')}] {m['data'][:1500]}")
repl.close()
