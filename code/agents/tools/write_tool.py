# tools/write_file_tool.py
from .base_tool import BaseTool
import os

class WriteToFileTool(BaseTool):
    name = "lean_write_file"
    description = "Write Lean4 code to a file in the results/ directory."
    parameters = {
        "path": "Relative file path inside results/ (use just filename, e.g., 'theorem.lean')",
        "content": "The code to write.",
    }

    def run(self, path: str, content: str) -> str:
        # Remove "results/" prefix if present
        normalized_path = path
        if path.startswith("results/") or path.startswith("results\\"):
            normalized_path = path[8:]
        
        safe_path = self.validate_path(normalized_path)
        try:
            # No need for os.makedirs since we're only writing to the root results/ dir
            with open(safe_path, "w", encoding="utf-8") as f:
                f.write(content)
            return f"Wrote file: {normalized_path}"
        except Exception as e:
            return f"__ERROR__: Could not write file: {repr(e)}"

