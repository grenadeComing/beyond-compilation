import json
import logging
import re
from pathlib import Path
from typing import Any, Dict, List, Optional

from .base_tool import BaseTool
from .run_lean_tool import LeanReplTool

logger = logging.getLogger(__name__)


class LeanInspectNameTool(BaseTool):

    name = "lean_inspect_name"
    description = (
        "Inspect a Lean identifier (e.g., via #check / #print) and return its type/signature and related information."
    )

    parameters = {
        "type": "object",
        "properties": {
            "name": {
                "type": "string",
                "description": "Lean identifier to inspect, e.g. 'Nat.Prime' or 'Filter.Tendsto'.",
            },
            "imports": {
                "type": "array",
                "items": {"type": "string"},
                "description": "Modules to import before inspection. Default ['Mathlib']",
            },
            "include_print": {
                "type": "boolean",
                "description": "If true, also run #print <name>. Default false.",
            },
        },
        "required": ["name"],
    }

    def __init__(self, repl_tool: LeanReplTool):
        super().__init__()
        if not isinstance(repl_tool, LeanReplTool):
            raise TypeError("repl_tool must be an instance of LeanReplTool")
        self.repl_tool = repl_tool

    @staticmethod
    def _safe_stem(s: str) -> str:
        s = re.sub(r"[^A-Za-z0-9_.-]+", "_", s)
        return (s[:100] if len(s) > 100 else s) or "tmp"

    @staticmethod
    def _extract_messages(repl_output_json: str) -> Dict[str, List[str]]:
        infos: List[str] = []
        errors: List[str] = []
        warnings: List[str] = []

        try:
            obj = json.loads(repl_output_json)
        except json.JSONDecodeError:
            return {"infos": [], "warnings": [], "errors": ["Unable to parse Lean output JSON"]}

        for msg in obj.get("messages", []):
            sev = msg.get("severity", "")
            data = msg.get("data", "")
            s = data if isinstance(data, str) else str(data)

            if sev == "info":
                infos.append(s)
            elif sev == "warning":
                warnings.append(s)
            elif sev == "error":
                errors.append(s)

        return {"infos": infos, "warnings": warnings, "errors": errors}

    def run(
        self,
        name: str,
        imports: Optional[List[str]] = None,
        include_print: bool = False,
        **_kwargs: Any,
    ) -> Dict[str, Any]:
        if not name or not isinstance(name, str) or not name.strip():
            return {"ok": False, "error": "name must be a non-empty string"}
        if self.allowed_root is None:
            return {"ok": False, "error": "allowed_root is not set in BaseTool."}

        imports = imports or ["Mathlib"]
        include_print = bool(include_print)

        import_lines = "\n".join([f"import {m}" for m in imports])
        cmds = [f"#check {name}"]
        if include_print:
            cmds.append(f"#print {name}")

        lean_code = import_lines + "\n\n" + "\n".join(cmds) + "\n"

        temp_path = Path(self.allowed_root) / f"inspect_{self._safe_stem(name)}.lean"

        try:
            temp_path.write_text(lean_code, encoding="utf-8")
        except Exception as e:
            logger.exception("Failed to write temporary Lean file")
            return {"ok": False, "error": f"Failed to write temp file: {type(e).__name__}: {e}"}

        try:
            repl_result = self.repl_tool.run(path=str(temp_path))
        finally:
            try:
                temp_path.unlink(missing_ok=True)
            except Exception:
                logger.warning("Failed to delete temporary Lean file: %s", temp_path)

        if not repl_result.get("ok"):
            return repl_result

        stdout = repl_result.get("stdout", "")
        stderr = repl_result.get("stderr", "")
        repl_output = repl_result.get("repl_output", "{}")

        msgs = self._extract_messages(repl_output)

        # First-principles "exists" criterion:
        # - If Lean emits an error for #check, it doesn't exist / doesn't typecheck in this context.
        exists = len(msgs["errors"]) == 0 and len(msgs["infos"]) > 0

        return {
            "ok": True,
            "name": name,
            "exists": exists,
            "infos": msgs["infos"],         # includes declaration line(s) from #check (and #print if enabled)
            "warnings": msgs["warnings"],
            "errors": msgs["errors"],
            "stdout": stdout,
            "stderr": stderr,
        }
