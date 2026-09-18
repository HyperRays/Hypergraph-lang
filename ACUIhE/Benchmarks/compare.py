#!/usr/bin/env python3
"""Compare retained, exactly paired benchmark cohorts; never invoke a solver."""

import argparse
import collections
import itertools
import json
import os
from pathlib import Path
import random
import statistics


def read(directory):
    metadata = json.loads((directory / "metadata.json").read_text())
    cases = [json.loads(s) for s in (directory / "cases.jsonl").read_text().splitlines()]
    runs = [json.loads(s) for s in (directory / "runs.jsonl").read_text().splitlines()]
    by_id = {c["id"]: c for c in cases}
    by_run = {(r["id"], r["mode"], r["repeat"]): r for r in runs}
    args = metadata["arguments"]
    expected = set(itertools.product(by_id, args["modes"], range(args["repeats"])))
    if len(by_id) != len(cases) or len(by_run) != len(runs) or set(by_run) != expected:
        raise ValueError(f"Incomplete or duplicate observations: {directory}")
    if any(r["status"] not in ("ok", "timeout") for r in runs):
        raise ValueError(f"Worker errors or label disagreements: {directory}")
    return metadata, by_id, by_run


def paired_inputs(before, after):
    bm, bc, br = before
    am, ac, ar = after
    if bc != ac or list(br) != list(ar):
        raise ValueError("Comparison requires identical cases, modes, repetitions and job order")
    cutoff = bm["arguments"]["timeout"]
    if cutoff != am["arguments"]["timeout"]:
        raise ValueError("Comparison requires identical cutoffs")
    pairs = []
    for case_id, case in bc.items():
        for mode in bm["arguments"]["modes"]:
            rr = range(bm["arguments"]["repeats"])
            old = [br[case_id, mode, i] for i in rr]
            new = [ar[case_id, mode, i] for i in rr]
            answers = {r["answer"] for r in old + new if r["status"] == "ok"}
            if len(answers) > 1 or (answers and case["expected"] is not None
                                   and answers != {case["expected"]}):
                raise ValueError(f"Answer disagreement: {case_id}, {mode}")
            old_ok = all(r["status"] == "ok" for r in old)
            new_ok = all(r["status"] == "ok" for r in new)
            pairs.append(dict(
                profile=case["profile"], mode=mode,
                stratum=tuple(case[k] for k in ("profile", "budget", "equations", "family")),
                old_ok=old_ok, new_ok=new_ok,
                old_cost=1000 * statistics.mean(min(cutoff, r["wall_s"]) for r in old),
                new_cost=1000 * statistics.mean(min(cutoff, r["wall_s"]) for r in new),
                ratio=(statistics.median(r["elapsed_ns"] for r in old) /
                       statistics.median(r["elapsed_ns"] for r in new)) if old_ok and new_ok else None))
    return pairs


def interval(rows, value, statistic, rng):
    """Resample paired inputs within the original fixed sampling cells."""
    cells = collections.defaultdict(list)
    for row in rows:
        cells[row["stratum"]].append(value(row))
    boot = sorted(statistic([v for cell in cells.values()
                            for v in rng.choices(cell, k=len(cell))]) for _ in range(2000))
    return boot[49], boot[1949]


def tables(rows, rng):
    profiles = sorted({r["profile"] for r in rows})
    groups = ([("all", rows)] if len(profiles) > 1 else [])
    groups += [(p, [r for r in rows if r["profile"] == p]) for p in profiles]
    lines = ["| profile | inputs | previous completed | current completed | newly completed | newly timed out | incomplete in both |",
             "|---|---|---|---|---|---|---|"]
    for name, group in groups:
        old = sum(r["old_ok"] for r in group)
        new = sum(r["new_ok"] for r in group)
        gained = sum(not r["old_ok"] and r["new_ok"] for r in group)
        lost = sum(r["old_ok"] and not r["new_ok"] for r in group)
        both = sum(not r["old_ok"] and not r["new_ok"] for r in group)
        n = len(group)
        lines.append(f"| {name} | {n} | {old}/{n} ({old/n:.1%}) | {new}/{n} ({new/n:.1%}) | {gained} | {lost} | {both} |")
    lines += ["", "| profile | previous mean capped wall ms | current mean capped wall ms | current − previous ms, paired 95% interval |",
              "|---|---|---|---|"]
    for name, group in groups:
        old = statistics.mean(r["old_cost"] for r in group)
        new = statistics.mean(r["new_cost"] for r in group)
        lo, hi = interval(group, lambda r: r["new_cost"] - r["old_cost"], statistics.mean, rng)
        lines.append(f"| {name} | {old:.2f} | {new:.2f} | {new-old:.2f} [{lo:.2f}, {hi:.2f}] |")
    lines += ["", "| profile | inputs completed in both | median per-input previous/current internal time ratio, 95% interval |",
              "|---|---|---|"]
    for name, group in groups:
        common = [r for r in group if r["ratio"] is not None]
        if common:
            lo, hi = interval(common, lambda r: r["ratio"], statistics.median, rng)
            median = statistics.median(r["ratio"] for r in common)
            lines.append(f"| {name} | {len(common)} | {median:.2f}× [{lo:.2f}, {hi:.2f}] |")
        else:
            lines.append(f"| {name} | 0 | — |")
    return lines


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cohort", nargs=3, action="append", required=True,
                        metavar=("NAME", "PREVIOUS", "CURRENT"))
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    rng = random.Random(20260910)
    lines = ["# Shared E-rule solver: historical benchmark comparison", "",
             "Every run uses the full ACUIhE solver. The current implementation replays the exact retained "
             "inputs with the same cutoff, modes, repetitions and shuffled job order. "
             "This analysis checks complete case records and the full observation grid before pairing. "
             "Completed answers agree between implementations and with every available independent label; "
             "the analysis rejects errors or disagreements. Timeouts remain unknown, not UNSAT answers.", "",
             "## How to read the comparisons", "",
             "An input is completed only when all its repetitions complete. Newly completed/timed-out "
             "counts compare this criterion. Capped wall cost is min(post-handshake wall time, cutoff), "
             "averaged over repetitions and then inputs. It includes communication/exit overhead. "
             "A timeout contributes the cutoff to this statistic only, not an observed runtime.", "",
             "Differences use 2,000 paired-input bootstrap resamples within the original "
             "profile/budget/equation-count/family cells. Intervals are pointwise 95% percentile intervals, "
             "not simultaneous guarantees. Input repetitions are not independent samples. "
             "Internal-time ratios first take each input's median per implementation, then their ratio "
             "(previous/current; larger than one favors current). They are conditional on completion "
             "in both implementations and do not measure the censored tail. Their intervals resample "
             "only this commonly completed subset, within its observed cells.", "",
             "The cohorts overlap: the paired and extended inputs are subsets of the primary cohort. "
             "Do not add their input counts. These are historical measurements, not contemporaneously "
             "interleaved executions. Machine load, clock frequency and thermal state are uncontrolled; "
             "bootstrap intervals do not account for that systematic uncertainty. These results do not "
             "establish asymptotic complexity or real-world workload performance. See "
             "[methodology](../README.md) and [current detailed results](SHARED_RULES_REPORT.md)."]
    hashes = set()
    for name, old_path, new_path in args.cohort:
        old_path, new_path = Path(old_path), Path(new_path)
        before, after = read(old_path), read(new_path)
        bm, am = before[0], after[0]
        if bm["arguments"]["seed"] != am["arguments"]["seed"]:
            raise ValueError("Shuffled job-order seeds differ")
        pairs = paired_inputs(before, after)
        hashes.add(am["executable_sha256"])
        lines += ["", f"## {name}", "",
                  f"{len(before[1])} inputs; cutoff {am['arguments']['timeout']:g} s; "
                  f"{am['arguments']['repeats']} repetition(s) per mode.", "",
                  f"Previous: {bm['timestamp_utc']}; current: {am['timestamp_utc']}.", "",
                  f"Raw data: [previous]({os.path.relpath(old_path, args.output.parent)}), "
                  f"[current]({os.path.relpath(new_path, args.output.parent)})."]
        for key in ("platform", "machine", "cpu_count", "lean_toolchain"):
            if bm[key] != am[key]:
                lines += ["", f"Environment difference, {key}: {bm[key]} → {am[key]}."]
        for mode in am["arguments"]["modes"]:
            lines += ["", f"### {mode}", ""] + tables([r for r in pairs if r["mode"] == mode], rng)
        lines += ["", f"Previous executable SHA-256: `{bm['executable_sha256']}`.", "",
                  f"Current executable SHA-256: `{am['executable_sha256']}`."]
    if len(hashes) != 1:
        raise ValueError("Current cohorts used different executables")
    args.output.write_text("\n".join(lines) + "\n")
    print(args.output)


if __name__ == "__main__":
    main()
