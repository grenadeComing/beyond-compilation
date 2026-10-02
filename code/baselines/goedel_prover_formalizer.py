#!/usr/bin/env python3
"""
One-shot Goedel-Prover runner for statement formalization.

This evaluates whether a prover-oriented Lean model transfers to NL-to-Lean
statement formalization. It deliberately uses the same statement-only prompt
family as the formalizer wrappers, rather than a proof-generation prompt.
"""

from __future__ import annotations

import sys

from vllm_formalizer import main


DEFAULT_ARGS = [
    "--model",
    "Goedel-LM/Goedel-Prover-V2-8B",
    "--output-name",
    "goedel_prover_v2_8b",
    "--prompt-style",
    "model-card",
    "--temperature",
    "0.6",
    "--top-p",
    "0.95",
    "--max-tokens",
    "4096",
]


if __name__ == "__main__":
    sys.argv = [sys.argv[0], *DEFAULT_ARGS, *sys.argv[1:]]
    main()
