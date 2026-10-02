import os
from abc import ABC, abstractmethod
from pathlib import Path


class BaseTool(ABC):
    allowed_root = None  # Set this at runtime to a base directory

    @classmethod
    def validate_path(cls, path: str) -> str:
        if cls.allowed_root is None:
            raise ValueError("allowed_root not set in BaseTool")

        root = Path(cls.allowed_root).resolve()
        abs_path = (root / path).resolve()

        try:
            abs_path.relative_to(root)
        except ValueError:
            raise ValueError(f"Disallowed path: {abs_path}")

        return str(abs_path)

    @abstractmethod
    def run(self, **kwargs):
        pass
