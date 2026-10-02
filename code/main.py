# main.py
import argparse
import json
import logging
import csv
import os
from pathlib import Path
import time
from typing import List, Dict, Any
from tqdm import tqdm
import concurrent.futures

from agents.runner import call_openai_lean_agent
from agents.tools.base_tool import BaseTool


def process_entry(
    entry: Dict[str, Any],
    lean_output_dir: Path,
    agent_log_dir: Path,
    config_name: str
) -> Dict[str, Any]:
    """
    Process a single one from the input file.
    """
    name = entry.get("id", entry["name"]).replace("|", "_")
    nl = entry["nl_statement"]
    output_path = lean_output_dir / f"{name}.lean"
    domain = entry.get("domain")

    try:
        logging.info(f"Processing: {name}")
        result = call_openai_lean_agent(
            file_path=str(output_path),
            natural_language_statement=nl,
            config=config_name,
            log_dir=str(agent_log_dir)
        )
        
        logging.info(f"Finished processing '{name}' with status: {result['status']} in {result['step']} steps.")

        lean4_code = ""
        io_error = None
        compile_status = result.get("compile_status", 0)

        if output_path.exists():
            try:
                with open(output_path, "r", encoding="utf-8") as f:
                    lean4_code = f.read()
            except Exception:
                logging.error(f"Error reading output file {output_path}.")
                io_error = "read_error"
                lean4_code = "Error reading Lean4 code"
        else:
            logging.warning(f"Output file {output_path} does not exist.")
            io_error = "file_missing"
            lean4_code = "Lean4 code file not found"

        return {
            "name": name,
            "domain": domain,
            "status": result["status"],
            "steps": result["step"],
            "compile_status": compile_status,
            "io_error": io_error,
            "nl_statement": nl,
            "lean4_code": lean4_code
        }

    # agent error exception handling
    except Exception as e:
        logging.error(f"Agent loading error when processing {name}: {e}")
        return {
            "name": name,
            "domain": domain,
            "status": "agent_crashed",
            "steps": 0,
            "compile_status": 0,
            "nl_statement": nl,
            "lean4_code": ""
        }

def setup_logging(log_path: Path) -> None:
    """Configure logging with the default 'INFO' level."""
    log_path.parent.mkdir(parents=True, exist_ok=True)
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(levelname)s - %(message)s',
        handlers=[
            logging.FileHandler(log_path, mode="a", encoding="utf-8"),
            logging.StreamHandler()
        ],
        force=True
    )

def print_final_summary(status_counts: Dict[str, int], total_processed: int):
    """Print the final summary statistics without needing the full stats list."""
    if total_processed == 0:
        logging.warning("No entries were processed successfully.")
        return
    
    passed_runs = status_counts.get("success", 0)
    pass_rate = (passed_runs / total_processed) * 100 if total_processed > 0 else 0

    print("\n" + "="*40)
    print("📊 Final Pass Rate Summary")
    print("="*40)
    print(f"Overall Pass Rate: {passed_runs} / {total_processed} ({pass_rate:.1f}%)")
    for status, count in status_counts.items():
        print(f"  {status}: {count}")
    print("=" * 40 + "\n")

def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run the Lean translation agent over the configured dataset."
    )
    parser.add_argument(
        "config",
        nargs="?",
        default="default",
        help="Name or path of the runner config to use (default: %(default)s).",
    )
    parser.add_argument("--input", default=None, help="Override input JSONL path.")
    parser.add_argument("--results-root", default=None,
                    help="Override results root dir (default: results/). "
                         "Use a separate root to keep experiments isolated.")
    return parser.parse_args()


def main(config_name: str = "default",
         input_override: str = None,
         results_root: str = None) -> None:
    PROJECT_ROOT = Path(__file__).resolve().parent
    RESULTS_ROOT = Path(results_root).resolve() if results_root else (PROJECT_ROOT / "results").resolve()
    RESULTS_ROOT.mkdir(parents=True, exist_ok=True)

    config_label = Path(config_name).stem or config_name
    config_results_dir = RESULTS_ROOT / f"config_{config_label}_results"

    lean_output_dir = config_results_dir / "lean_output"
    agent_log_dir = config_results_dir / "agent_logs"
    for directory in (lean_output_dir, agent_log_dir):
        directory.mkdir(parents=True, exist_ok=True)

    setup_logging(config_results_dir / "translation.log")

    # The input file
    INPUT_FILE = Path(input_override) if input_override else (PROJECT_ROOT.parent / "benchmark/benchmark.jsonl")   #
    MAX_WORKERS = int(os.environ.get("MAX_WORKERS", 3))

    # Set the allowed root path for all tools
    BaseTool.allowed_root = str(lean_output_dir)
    logging.info(f"Set allowed_root to: {lean_output_dir}")

    logging.info(f"Loading input data from {INPUT_FILE}...")
    try:
        with open(INPUT_FILE, "r", encoding="utf-8") as f:
            entries = [json.loads(line) for line in f]
        """# --- TEMPORARY slice selection (remove when processing all entries again) ---
        selected_entries: List[Dict[str, Any]] = []
        slice_specs = [
            (100, 110),# [100:105]
        ]
        if slice_specs:
            for start, end in slice_specs:
                if start >= len(entries):
                    continue
                selected_entries.extend(entries[start:min(end, len(entries))])
            
            entries = selected_entries[:20]  # ensure we only keep at most 20 total
            logging.info(f"Limiting processing to {len(entries)} selected entries based on predefined slices.")
        # --- END TEMPORARY slice selection ---"""
        logging.info(f"Loaded {len(entries)} entries to process.")
    except Exception as e:
        logging.error(f"Failed to load input data: {e}")
        raise

    # Create a CSV file and write the headers
    stats_file = config_results_dir / "agent_run_summary.csv"
    csv_file = open(stats_file, "w", newline="", encoding="utf-8")
    csv_writer = csv.writer(csv_file)
    csv_writer.writerow(["name", "domain", "status", "steps", "compile_status", "io_error", "nl_statement", "lean4_code"])
    csv_file.flush()  # Ensure header is written immediately
    
    # Counters for final statistics
    status_counts = {}
    total_processed = 0
    
    logging.info(f"Starting parallel processing with up to {MAX_WORKERS} threads...")
    time_start = time.perf_counter()
    try:
        # Use ThreadPoolExecutor instead of ProcessPoolExecutor
        with concurrent.futures.ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
            # Submit all jobs directly
            future_to_entry = {
                executor.submit(process_entry, entry, lean_output_dir, agent_log_dir, config_name): entry 
                for entry in entries
            }
            
            # Process completed results as they finish
            with tqdm(total=len(entries), desc="Processing entries") as pbar:
                for future in concurrent.futures.as_completed(future_to_entry):
                    try:
                        stat = future.result()
                        if stat:
                            # Write immediately to CSV
                            csv_writer.writerow([
                                stat["name"], 
                                stat["domain"], 
                                stat["status"], 
                                stat["steps"], 
                                stat.get("compile_status"),
                                stat.get("io_error"), 
                                stat["nl_statement"], 
                                stat["lean4_code"]
                            ])
                            csv_file.flush()  # Ensure data is written to disk
                            
                            # Update counters for final summary
                            status_counts[stat["status"]] = status_counts.get(stat["status"], 0) + 1
                            total_processed += 1
                            
                            # Update progress bar with current status
                            pbar.set_postfix({"Status": stat["status"], "Name": stat["name"][:20]})
                    except Exception as e:
                        entry = future_to_entry[future]
                        logging.error(f"Error processing {entry.get('name', 'unknown')}: {e}")
                    finally:
                        pbar.update(1)
    
    finally:
        # Always close the CSV file
        csv_file.close()


    time_end = time.perf_counter()
    # Print final statistics using the counters
    print_final_summary(status_counts, total_processed)
    print(f"Total processing time: {time_end - time_start:.2f} seconds")

if __name__ == "__main__":
    args = parse_args()
    main(args.config, input_override=args.input, results_root=args.results_root)
