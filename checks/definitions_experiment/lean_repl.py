"""Minimal driver for the Lean REPL (leanprover-community/repl): load Mathlib once, then run commands in that env."""

from __future__ import annotations

import json
import os
import subprocess

REPL_DIR = os.environ.get("LEAN_REPL_DIR", "repl")


class Repl:
    def __init__(self) -> None:
        self.p = subprocess.Popen(["lake", "exe", "repl"], cwd=REPL_DIR, stdin=subprocess.PIPE,
                                  stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, bufsize=1)
        self.base = self.send({"cmd": "import Mathlib"})["env"]

    def send(self, obj: dict) -> dict:
        self.p.stdin.write(json.dumps(obj) + "\n\n")
        self.p.stdin.flush()
        lines = []
        while True:
            line = self.p.stdout.readline()
            if line == "":
                raise RuntimeError("REPL exited: " + self.p.stderr.read()[-2000:])
            if line.strip() == "" and lines:
                break
            if line.strip():
                lines.append(line)
        return json.loads("".join(lines))

    def run(self, code: str) -> dict:
        return self.send({"cmd": code, "env": self.base})

    def close(self) -> None:
        self.p.kill()
