#!/usr/bin/env python3
"""
One-shot Kimina-Autoformalizer runner.

This is a thin wrapper around vllm_formalizer.py with Kimina's model-card
prompt defaults. User-provided CLI flags still override these defaults.
"""

from __future__ import annotations

import sys

from vllm_formalizer import main


DEFAULT_ARGS = [
    "--model",
    "AI-MO/Kimina-Autoformalizer-7B",
    "--output-name",
    "kimina_autoformalizer_7b",
    "--prompt-style",
    "model-card",
    "--temperature",
    "0.6",
    "--top-p",
    "0.95",
    "--max-tokens",
    "2048",
]


if __name__ == "__main__":
    sys.argv = [sys.argv[0], *DEFAULT_ARGS, *sys.argv[1:]]
    main()
