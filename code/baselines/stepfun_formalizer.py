#!/usr/bin/env python3
"""
One-shot StepFun-Formalizer runner.

This is a thin wrapper around vllm_formalizer.py with StepFun's model-card
prompt defaults. User-provided CLI flags still override these defaults.
"""

from __future__ import annotations

import sys

from vllm_formalizer import main


DEFAULT_ARGS = [
    "--model",
    "stepfun-ai/StepFun-Formalizer-7B",
    "--output-name",
    "stepfun_7b",
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
