import os
# in agents/tools/translator_tool.py
import requests
import logging
from typing import List, Dict, Any
from .base_tool import BaseTool

class LeanTranslationTool(BaseTool):
    name = "lean4_translation"
    description = (
        "Produce Lean4 code corresponding to a natural-language mathematical statement using a fine-tuned model"
    )

    # Fixed schema structure
    parameters = {
        "type": "object",
        "properties": {
            "natural_language_statement": {
                "type": "string",
                "description": "The natural language statement to translate."
            },
            "retrieved_examples": {
                "type": "array",
                "description": "A list of example dicts like [{\"nl\": ..., \"lean\": ...}]. Only top 5 will be used.",
                "items": {
                    "type": "object",
                    "properties": {
                        "nl": {"type": "string"},
                        "lean": {"type": "string"}
                    },
                    "required": ["nl", "lean"]
                }
            }
        },
        "required": ["natural_language_statement"]
    }

    DEFAULT_MODEL = "FrenzyMath/Herald_translator"
    DEFAULT_API_URL = os.environ.get("HERALD_API_URL", "http://localhost:8000/v1/chat/completions")

    def __init__(self, api_url: str | None = None):
        super().__init__()
        self.api_url = api_url or self.DEFAULT_API_URL

    def run(
        self,
        natural_language_statement: str,
        retrieved_examples: List[Dict[str, Any]] | None = None,
        **kwargs,
    ) -> Dict[str, Any]:
        try:
            messages: List[Dict[str, Any]] = [
                {
                    "role": "user",
                    "content": (
                        "Translate the following natural language statement to Lean4 code. "
                        "Import Mathlib and end the declaration with := by sorry.\n\n"
                        f"Statement:\n{natural_language_statement}"
                    )
                }
            ]
            retrieved_context = ""
            if retrieved_examples:
                valid_examples = [ex for ex in retrieved_examples if isinstance(ex, dict)]
                if len(valid_examples) != len(retrieved_examples):
                    logging.warning("Some items in retrieved_examples were not dictionaries and have been filtered out.")

                examples_to_use = valid_examples[:5]
                logging.info(f"Translator using {len(examples_to_use)} examples for context.")
                examples_str = "\n\n---\n\n".join(
                    [f"NL: {ex.get('nl', '')}\nLean:\n```lean\n{ex.get('lean', '')}\n```" for ex in examples_to_use]
                )
                retrieved_context = f"Here are some similar examples for context:\n\n{examples_str}\n\n"

            if retrieved_context:
                final_prompt = (
                    "Below are some examples of natural language statements and their corresponding Lean4 translations, use at Chain-of-Thought to help you translate the new statement.\n\n"
                    f"{retrieved_context}"
                )
                messages.append({"role": "user", "content": final_prompt})

            resp = requests.post(
                self.api_url,
                json={"model": self.DEFAULT_MODEL, "messages": messages, "temperature": 0.2}
            )

            if resp.status_code != 200:
                return {"ok": False, "error": f"API error: {resp.status_code} {resp.text}"}

            reply = resp.json()["choices"][0]["message"]["content"]
            return {"ok": True, "lean_translation": reply.strip()}

        except Exception as e:
            return {"ok": False, "error": f"LeanTranslationTool exception: {e}"}
