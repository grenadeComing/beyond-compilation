import difflib
import re
from typing import Any, Dict, List, Optional

from .base_tool import BaseTool
from .lean_inspect_name_tool import LeanInspectNameTool


class LeanResolveNameTool(BaseTool):
    name = "lean_resolve_name"
    description = (
        "Given a token or partial name, return candidate Lean/Mathlib identifiers that may match it."
    )

    parameters = {
        "type": "object",
        "properties": {
            "token": {
                "type": "string",
                "description": "Ambiguous token, e.g. 'Prime', 'Cauchy', 'tendsto'.",
            },
            "top_k": {
                "type": "integer",
                "description": "Number of verified candidates to return. Default 10.",
            },
            "imports": {
                "type": "array",
                "items": {"type": "string"},
                "description": "Modules to import when checking candidates. Default ['Mathlib']",
            },
            "namespace_hints": {
                "type": "array",
                "items": {"type": "string"},
                "description": "Optional namespaces to try, e.g. ['Nat','Real','Filter'].",
            },
            "extra_candidates": {
                "type": "array",
                "items": {"type": "string"},
                "description": "Optional extra identifiers to include (e.g., from retrieval results).",
            },
            "max_candidates": {
                "type": "integer",
                "description": "Safety cap on how many candidates to check. Default 80.",
            },
        },
        "required": ["token"],
    }

    def __init__(self, inspect_tool: LeanInspectNameTool):
        super().__init__()
        self.inspect_tool = inspect_tool

    @staticmethod
    def _dedupe_keep_order(xs: List[str]) -> List[str]:
        seen = set()
        out: List[str] = []
        for x in xs:
            if x not in seen:
                seen.add(x)
                out.append(x)
        return out

    @staticmethod
    def _default_namespaces() -> List[str]:
        # High-yield, broadly useful namespaces; customize per your dataset domain.
        return [
            "Nat", "Int", "Rat", "Real",
            "Set", "Function",
            "Finset", "Fintype",
            "Order",
            "Algebra", "Ring", "Group", "Monoid",
            "LinearAlgebra",
            "Topology", "Metric", "UniformSpace",
            "Filter",
            "MeasureTheory",
        ]

    @staticmethod
    def _case_variants(tok: str) -> List[str]:
        vs = [tok]
        if tok and tok[0].islower():
            vs.append(tok[0].upper() + tok[1:])
        if tok and tok[0].isupper():
            vs.append(tok[0].lower() + tok[1:])
        return vs

    @staticmethod
    def _is_identifier_like(s: str) -> bool:
        # Accept Lean-ish identifiers with dots and apostrophes.
        return bool(re.match(r"^[A-Za-z_][A-Za-z0-9_'.]*(\.[A-Za-z_][A-Za-z0-9_'.]*)*$", s))

    def _generate_candidates(self, token: str, namespace_hints: Optional[List[str]]) -> List[str]:
        token = token.strip()
        if not token:
            return []

        # Already qualified -> mostly trust it, plus mild cleanup.
        if "." in token:
            cands = [token, token.lstrip("_")]
            return self._dedupe_keep_order([c for c in cands if self._is_identifier_like(c)])

        ns_list = namespace_hints or self._default_namespaces()
        cands: List[str] = []

        for cv in self._case_variants(token):
            cands.append(cv)
            for ns in ns_list:
                cands.append(f"{ns}.{cv}")

        # Common naming pattern: IsX
        if token and token[0].isupper() and not token.startswith("Is"):
            cands.append("Is" + token)
            for ns in ns_list:
                cands.append(f"{ns}.Is{token}")

        cands = [c for c in cands if self._is_identifier_like(c)]
        return self._dedupe_keep_order(cands)

    @staticmethod
    def _score(token: str, cand: str, infos: List[str]) -> float:
        # First-principles score: lexical similarity + tiny bonus if the type mentions token.
        last = cand.split(".")[-1]
        sim = difflib.SequenceMatcher(None, token.lower(), last.lower()).ratio()

        bonus = 0.0
        if last.lower() == token.lower():
            bonus += 0.25
        if cand.lower().endswith("." + token.lower()):
            bonus += 0.15
        if any(token.lower() in s.lower() for s in infos):
            bonus += 0.05

        return sim + bonus

    def run(
        self,
        token: str,
        top_k: int = 10,
        imports: Optional[List[str]] = None,
        namespace_hints: Optional[List[str]] = None,
        extra_candidates: Optional[List[str]] = None,
        max_candidates: int = 10,
        **_kwargs: Any,
    ) -> Dict[str, Any]:
        if not token or not isinstance(token, str) or not token.strip():
            return {"ok": False, "error": "token must be a non-empty string"}
        if self.allowed_root is None:
            return {"ok": False, "error": "allowed_root is not set in BaseTool."}

        imports = imports or ["Mathlib"]
        top_k = max(1, min(int(top_k) if top_k else 10, 50))
        max_candidates = max(10, min(int(max_candidates) if max_candidates else 80, 200))

        generated = self._generate_candidates(token, namespace_hints=namespace_hints)
        extras = [x.strip() for x in (extra_candidates or []) if isinstance(x, str) and x.strip()]
        extras = [x for x in extras if self._is_identifier_like(x)]

        pool = self._dedupe_keep_order([*generated, *extras])
        pool = pool[:max_candidates]

        # Ensure inspect tool shares the same allowed_root (temp-file workspace)
        self.inspect_tool.allowed_root = self.allowed_root

        verified: List[Dict[str, Any]] = []
        for cand in pool:
            r = self.inspect_tool.run(name=cand, imports=imports, include_print=False)
            if not r.get("ok"):
                continue
            if not r.get("exists"):
                continue
            infos = r.get("infos", []) or []
            verified.append(
                {
                    "name": cand,
                    "score": self._score(token, cand, infos),
                    "infos": infos,  # typically contains the declaration line from #check
                }
            )

        verified.sort(key=lambda x: x["score"], reverse=True)
        verified = verified[:top_k]

        return {
            "ok": True,
            "token": token,
            "candidates": verified,
            "checked_count": len(pool),
            "imports": imports,
        }
