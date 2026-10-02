import os
import requests
from .base_tool import BaseTool


class SearchOnlineTool(BaseTool):
    name = "search_online"
    description = "Search the web and return results for a query."

    parameters = {
        "query": "Search query"
    }

    SERPER_URL = "https://google.serper.dev/search"

    def __init__(self):
        self.api_key = os.getenv("SERPER_API_KEY")
        if not self.api_key:
            raise RuntimeError("Missing SERPER_API_KEY")

        self.session = requests.Session()
        self.session.headers.update({
            "X-API-KEY": self.api_key,
            "Content-Type": "application/json",
        })

    def run(self, query: str) -> dict:
        try:
            payload = {
                "q": query,
                "num": 5
            }

            resp = self.session.post(self.SERPER_URL, json=payload, timeout=15)

            if resp.status_code != 200:
                return {
                    "ok": False,
                    "error": f"Serper error {resp.status_code}: {resp.text}"
                }

            data = resp.json()

            # Just return Google's organic results as-is
            return {
                "ok": True,
                "results": data.get("organic", [])
            }

        except Exception as e:
            return {
                "ok": False,
                "error": f"SearchOnlineTool exception: {e}"
            }
