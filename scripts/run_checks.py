#!/usr/bin/env python3
"""Run the five independent finite checks; no third-party Python packages needed."""
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
CHECKS = {
    "chore_primitives": "experiments/chores/check_primitives.py",
    "chore_ledger": "experiments/chores/check_ledger.py",
    "randomized_upper": "experiments/upper/check_finite.py",
    "randomized_lower": "experiments/lower/check_lower.py",
    "mixed": "experiments/mixed/independent_checks.py",
}


def run_one(name, relative):
    source = ROOT / relative
    run = subprocess.run([sys.executable, str(source)], cwd=ROOT,
                         text=True, capture_output=True, check=True)
    result = json.loads(run.stdout)
    if result.get("status", "passed") != "passed":
        raise RuntimeError(f"{name}: check did not pass")
    target = source.with_name(name + "_result.json")
    target.write_text(json.dumps(result, indent=2) + "\n")
    return name, {"status": "passed", "script": relative,
                  "script_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                  "result": str(target.relative_to(ROOT))}


def main():
    results = {}
    with ThreadPoolExecutor(max_workers=4) as pool:
        futures = [pool.submit(run_one, name, path) for name, path in CHECKS.items()]
        for future in as_completed(futures):
            name, record = future.result()
            results[name] = record
            print(f"{name}: passed", flush=True)
    report = {"status": "passed", "checked_at_utc": datetime.now(timezone.utc).isoformat(),
              "checks": dict(sorted(results.items())),
              "scope": "Finite exact-arithmetic checks only; not proofs of the continuous theorems."}
    (ROOT / "verification/finite_checks.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
