"""Run one or more Lean files on top of `import Mathlib` (loaded once) and print the messages.

    python run_lean.py FILE.lean [FILE2.lean ...]

Import lines in the files are ignored (Mathlib is already loaded). Lean v4.22.0-rc4, the paper's Mathlib.
"""

import sys
from pathlib import Path

from lean_repl import Repl

repl = Repl()
for path in sys.argv[1:]:
    code = "\n".join(l for l in Path(path).read_text().splitlines() if not l.strip().startswith("import "))
    res = repl.run(code)
    print(f"===== {path}")
    msgs = res.get("messages", [])
    if not msgs:
        print("(no messages)")
    for m in msgs:
        pos = m.get("pos", {})
        print(f"[{m['severity']} line {pos.get('line')}] {m['data']}")
repl.close()
