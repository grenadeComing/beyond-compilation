import os
from .base_tool import BaseTool
from pathlib import Path
from typing import Dict, Any
import subprocess
import json
import logging


class LeanReplTool(BaseTool):
    name = "lean4_repl_runner"
    description = "Run the Lean4 compiler / REPL on the given Lean file and return whether it compiles, along with diagnostic output."
    parameters = {
        "type": "object",
        "properties": {
            "path": {
                "type": "string",
                "description": "The path to the Lean4 file to run."
            }
        },
        "required": ["path"]
    }

    REPL_DIR = os.environ.get("LEAN_REPL_DIR", "repl")  # path to a built leanprover-community/repl checkout

    @staticmethod
    def _contains_unknown_constant(text: Any) -> bool:
        return isinstance(text, str) and "unknown constant" in text.lower()

    @staticmethod
    def _mentions_deprecated(text: Any) -> bool:
        if isinstance(text, str):
            return "deprecated" in text.lower()
        if isinstance(text, list):
            return any(LeanReplTool._mentions_deprecated(entry) for entry in text)
        return False

    def run(self, path: str, **kwargs) -> Dict[str, Any]:
        try:
            full_path = self.validate_path(path)
        except ValueError as e:
            return {"ok": False, "repl_pass": 0, "error": str(e)}

        payload = json.dumps({
            "path": str(Path(full_path).resolve()),
            "allTactics": True
        }) + "\n\n"

        try:
            process = subprocess.Popen(
                ["lake", "exe", "repl"],
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                cwd=self.REPL_DIR,
            )

            stdout, stderr = process.communicate(payload, timeout=80)
            stdout, stderr = stdout.strip(), stderr.strip()

            repl_pass = 0
            obj = None
            has_errors = False

            # ---- Parse REPL JSON ----
            if stdout:
                try:
                    obj = json.loads(stdout)
                except json.JSONDecodeError:
                    has_errors = True  # invalid output is also an error
                if self._mentions_deprecated(stdout):
                    has_errors = True
            else:
                has_errors = True

            # ---- process-level errors ----
            if process.returncode != 0:
                has_errors = True

            if stderr:
                has_errors = True
                if self._mentions_deprecated(stderr):
                    has_errors = True

            # ---- semantic-level errors inside REPL JSON ----
            if obj is not None:
                top_level_msg = obj.get("message", "")
                if isinstance(top_level_msg, str):
                    lower_msg = top_level_msg.lower()

                    # detect missing-file problems
                    if "no such file" in lower_msg or "no such file or directory" in lower_msg:
                        has_errors = True

                    # detect unknown constants
                    if "unknown constant" in lower_msg:
                        has_errors = True

                    if self._mentions_deprecated(top_level_msg):
                        has_errors = True

                # inspect deep messages
                all_messages = []

                def collect(candidate):
                    if isinstance(candidate, list):
                        for entry in candidate:
                            if isinstance(entry, dict):
                                all_messages.append(entry)

                collect(obj.get("messages"))
                for tactic in obj.get("tactics", []):
                    if isinstance(tactic, dict):
                        collect(tactic.get("messages"))

                for entry in all_messages:
                    sev = entry.get("severity", "").lower()
                    data_text = entry.get("data") or entry.get("message")
                    if sev == "error" or ("unknown constant" in str(data_text).lower()):
                        has_errors = True
                        break
                    if sev == "warning" and self._mentions_deprecated(data_text):
                        has_errors = True
                        break

            # ---- Pass if NO error detected ----
            if not has_errors:
                repl_pass = 1

            return {
                "ok": True,
                "repl_pass": repl_pass,
                "repl_output": stdout or "{}",
                "stdout": stdout,
                "stderr": stderr
            }

        except subprocess.TimeoutExpired:
            process.kill()
            return {"ok": False, "repl_pass": 0, "error": "Lean REPL timed out."}

        except Exception as e:
            return {"ok": False, "repl_pass": 0, "error": str(e)}
