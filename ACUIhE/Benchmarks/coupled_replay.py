"""Replay connected-system scaling probes; measurements are not formal proofs."""
import argparse
import collections
import hashlib
import json
from pathlib import Path
import platform
import random
import statistics

import fuzz


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cases", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=float, default=5.0)
    parser.add_argument("--repeats", type=int, default=3)
    args = parser.parse_args()
    cases = json.loads(args.cases.read_text())
    root = Path(__file__).resolve().parent.parent
    exe = root / ".lake/build/bin/acuihe_bench"
    args.output.mkdir(parents=True, exist_ok=False)
    (args.output / "cases.json").write_text(json.dumps(cases, indent=2) + "\n")
    metadata = dict(executable=str(exe), executable_sha256=hashlib.sha256(exe.read_bytes()).hexdigest(),
                    cutoff_s=args.timeout, repeats=args.repeats, platform=platform.platform(),
                    timing="Fresh-process post-parse handshake; all solver preprocessing included",
                    scope="Deterministic connected families, not random-workload sampling")
    (args.output / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    jobs = [(c, r) for c in cases for r in range(args.repeats)]
    random.Random(20260910).shuffle(jobs)
    results = []
    with (args.output / "runs.jsonl").open("x") as stream:
        for case, repeat in jobs:
            result = dict(id=case["id"], repeat=repeat,
                          **fuzz.measure(exe, case, "decision", args.timeout))
            results.append(result)
            stream.write(json.dumps(result) + "\n")
            stream.flush()
            print(json.dumps(result), flush=True)
            if result["status"] == "mismatch":
                raise RuntimeError(result)
    summary = []
    for case in cases:
        runs = [r for r in results if r["id"] == case["id"]]
        times = [r["elapsed_ns"] / 1e6 for r in runs if r["status"] == "ok"]
        summary.append(dict(id=case["id"], statuses=dict(collections.Counter(r["status"] for r in runs)),
                            completed_median_ms=statistics.median(times) if times else None))
    (args.output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")


if __name__ == "__main__":
    main()
