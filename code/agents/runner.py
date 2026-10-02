import os
import json
import logging
import re
from pathlib import Path
from typing import Dict, Any, List, Optional
from openai import OpenAI
import litellm
litellm.suppress_debug_info = True
from agents.tools import *

logging.basicConfig(level=logging.INFO)
logging.getLogger("LiteLLM").setLevel(logging.WARNING)
logging.getLogger("litellm").setLevel(logging.WARNING)
lean_repl_tool_instance = LeanReplTool()
lean_inspect_tool_instance = LeanInspectNameTool(lean_repl_tool_instance)
lean_resolve_tool_instance = LeanResolveNameTool(lean_inspect_tool_instance)

# all possible tools
TOOLS: Dict[str, Any] = {
    "lean4_translation": LeanTranslationTool(),
    "lean_write_file": WriteToFileTool(),
    "lean4_repl_runner": lean_repl_tool_instance,
    "search_online": SearchOnlineTool(),
    "lean_inspect_name": lean_inspect_tool_instance,
    "lean_resolve_name": lean_resolve_tool_instance,
    
}

BASE_DIR = Path(__file__).resolve().parent
CONFIGS_DIR = BASE_DIR / "configs"


def _resolve_config_path(config: Optional[str]) -> Path:
    if config is None:
        path = CONFIGS_DIR / "default.json"
    else:
        candidate = Path(config)
        if candidate.is_absolute():
            path = candidate
        else:
            if not candidate.suffix:
                candidate = candidate.with_suffix(".json")
            path = CONFIGS_DIR / candidate
            if not path.exists():
                path = BASE_DIR / candidate
    path = path.resolve()
    if not path.exists():
        raise FileNotFoundError(f"Runner config not found: {path}")
    return path


# read the config file and load the system prompt accordingly
def _load_runner_config(path_str: str) -> Dict[str, Any]:
    path = Path(path_str).resolve()
    with open(path, "r", encoding="utf-8") as f:
        cfg = json.load(f)

    prompt_path = Path(cfg["system_prompt_file"])
    if not prompt_path.is_absolute():
        prompt_path = (path.parent / prompt_path).resolve()

    with open(prompt_path, "r", encoding="utf-8") as pf:
        cfg["system_prompt"] = pf.read().strip()

    cfg["enabled_tools"] = list(cfg["enabled_tools"])
    return cfg

def _tool_spec(tool_obj: Any) -> Dict[str, Any]:
    """
    Generate OpenAI tool specification from a tool object.
    Now handles both simple string parameters and complex schema objects.
    """
    # Check if the tool has a complex parameters schema (new format)
    if hasattr(tool_obj, 'parameters') and isinstance(tool_obj.parameters, dict) and 'type' in tool_obj.parameters:
        # This is a complex schema - use it directly
        return {
            "type": "function",
            "function": {
                "name": tool_obj.name,
                "description": tool_obj.description,
                "parameters": tool_obj.parameters,  # Use the schema as-is
            },
        }
    else:
        # Fall back to the old simple string format for backward compatibility
        return {
            "type": "function",
            "function": {
                "name": tool_obj.name,
                "description": tool_obj.description,
                "parameters": {
                    "type": "object",
                    "properties": { name: {"type": "string", "description": desc} for name, desc in tool_obj.parameters.items() },
                    "required": list(tool_obj.parameters.keys()),
                },
            },
        }

def _repl_passed(result_str: str) -> bool:
    """Check if lean4_repl_runner indicates success"""
    if "'repl_pass': 1" in result_str or '"repl_pass": 1' in result_str:
        return True
    return False

# ===================================================agent logic
def call_openai_lean_agent(
    file_path: str,
    natural_language_statement: str,
    log_dir: str,
    timeout_sec: float = 180.0,
    config: str = "default",
) -> Dict[str, Any]:

    log_path = os.path.join(log_dir, f"{Path(file_path).stem}.jsonl")

    config_path = _resolve_config_path(config)
    config_data = _load_runner_config(str(config_path))

    # quick check of tools
    enabled_tool_names = config_data.get("enabled_tools") or list(TOOLS.keys())
    missing_tools = [name for name in enabled_tool_names if name not in TOOLS]
    if missing_tools:
        raise ValueError(f"Config requests unknown tools: {missing_tools}")

    def log(action, **kwargs):
        event = {"action": action, **kwargs}
        with open(log_path, "a", encoding="utf-8") as f:
            f.write(json.dumps(event, ensure_ascii=False) + "\n")

    system_prompt = config_data.get("system_prompt")
    max_steps = config_data.get("max_steps")
    model_to_use = config_data.get("model")

    # Use LiteLLM for non-OpenAI models, native OpenAI client otherwise
    use_litellm = any(model_to_use.startswith(p) for p in ["anthropic/", "gemini/", "claude-"])
    client = None if use_litellm else OpenAI()

    agent_tools = {name: TOOLS[name] for name in enabled_tool_names}
    tool_specs = [_tool_spec(t) for t in agent_tools.values()]

    # build the initial messages
    messages: List[Dict[str, Any]] = [
        {"role": "system", "content": system_prompt},
        {
            "role": "user",
            "content": (
                f"Translate the following and check correctness: {natural_language_statement}\n"
                f"Save it to: {Path(file_path).name}"
            ),
        },
    ]

    pending_repl_fix = False  # becomes True when last REPL failed
    repl_tool = lean_repl_tool_instance

    def run_repl_check(reason: str) -> int:
        try:
            result = repl_tool.run(path=file_path)
            passed = False
            if isinstance(result, dict):
                passed = result.get("repl_pass") == 1
            result_snippet = str(result)
            if not passed:
                passed = _repl_passed(result_snippet)
            log("compile_check", step=reason, passed=passed, result=result_snippet[:500])
            return 1 if passed else 0
        except Exception as err:
            log("compile_check_error", step=reason, error=str(err))
            return 0

    def finish(status: str, step_value: int, outcome: str) -> Dict[str, Any]:
        compile_status = run_repl_check(outcome)
        log("run_complete", outcome=outcome, step=step_value, compile_status=compile_status)
        return {
            "status": status,
            "step": step_value,
            "log_path": log_path,
            "compile_status": compile_status,
        }

    for step in range(1, max_steps + 1):
        # Call model (retry transient errors up to MAX_MODEL_RETRIES times)
        msg = None
        for attempt in range(1, 4):
            try:
                if use_litellm:
                    response = litellm.completion(
                        model=model_to_use,
                        tools=tool_specs,
                        tool_choice="auto",
                        messages=messages,
                        timeout=timeout_sec
                    )
                else:
                    response = client.chat.completions.create(
                        model=model_to_use,
                        tools=tool_specs,
                        tool_choice="auto",
                        messages=messages,
                        timeout=timeout_sec
                    )
                msg = response.choices[0].message
                break
            except Exception as e:
                log("agent_API_error", step=step, attempt=attempt, error=str(e))
                if attempt == 3:
                    return finish("agent_API_error", step, "agent_API_error")
                continue

        # append the message accordingly
        assistant_msg = {
            "role": "assistant",
            "content": msg.content or ""
        }
        if msg.tool_calls:
            # Only keep the first tool call to match execution logic
            tc = msg.tool_calls[0]
            assistant_msg["tool_calls"] = [
                {
                    "id": tc.id,
                    "type": "function",
                    "function": {
                        "name": tc.function.name,
                        "arguments": tc.function.arguments
                    }
                }
            ]
        messages.append(assistant_msg)

        log("model_reply:", step=step, 
            has_tools=bool(msg.tool_calls),
            content=msg.content[:200] if msg.content else None,
            tools_requested=[tc.function.name for tc in msg.tool_calls or []])

        # Check explicit success, then quit immediately
        explicit_success = False
        if msg.content:
            try:
                parsed_content = json.loads(msg.content)
            except json.JSONDecodeError:
                parsed_content = None

            if isinstance(parsed_content, dict):
                explicit_success = parsed_content.get("status") == "success"
            elif re.search(r'"status"\s*:\s*"success"', msg.content):
                explicit_success = True

        if explicit_success:
            if pending_repl_fix:
                log("success_blocked", step=step, reason="repl_failed")
                messages.append({
                    "role": "user",
                    "content": (
                        "Lean still reports repl_pass = 0. Fix the Lean file and rerun "
                        "lean4_repl_runner before declaring success."
                    )
                })
                continue
            log("success", step=step, type="explicit")
            return finish("success", step, "explicit_success")
        
        # if not quit, there should be a tool call
        if msg.tool_calls:
            tc = msg.tool_calls[0]   # Only call the first tool
            try:
                args = json.loads(tc.function.arguments or "{}")
                result_obj = TOOLS[tc.function.name].run(**args)
                result_str = (result_obj if isinstance(result_obj, str)
                            else json.dumps(result_obj, ensure_ascii=False))
                log("tool_run_result", step=step, tool=tc.function.name, ok=True,
                    args=args, result=result_str[:500])
            except Exception as e:
                result_str = f"ERROR: {e}"
                log("tool_run", step=step, tool=tc.function.name, ok=False,
                    args=tc.function.arguments, result=result_str)

            messages.append({"role": "tool", "tool_call_id": tc.id, "content": result_str})

            # Auto-success on REPL pass
            is_repl_pass = False
            if tc.function.name == "lean4_repl_runner":
                repl_pass_value = None
                if isinstance(result_obj, dict):
                    repl_pass_value = result_obj.get("repl_pass")
                if repl_pass_value is None and _repl_passed(result_str):
                    repl_pass_value = 1

                if repl_pass_value == 1:
                    is_repl_pass = True
                    pending_repl_fix = False
                else:
                    pending_repl_fix = True
            elif tc.function.name == "lean_write_file" and pending_repl_fix:
                # allow continued editing but still require a successful REPL
                pass
            else:
                # Non-REPL tools do not change the pending flag
                pass

            if is_repl_pass:
                log("success", step=step, type="repl_pass")
                return finish("success", step, "repl_pass")

    if repl_tool is not None and Path(file_path).exists():
        try:
            repl_result = repl_tool.run(path=file_path)
            if isinstance(repl_result, dict) and repl_result.get("repl_pass") == 1:
                log("success", step=max_steps, type="post_repl")
                return finish("success", max_steps, "post_repl")
        except Exception as repl_error:
            log("post_repl_error", step=max_steps, error=str(repl_error))

    log("max_steps_reached", steps=max_steps)
    return finish("max_steps_reached", max_steps, "max_steps")
