#!/usr/bin/env python3
"""Run reproducible ACUIhE solver fuzz benchmarks."""

from __future__ import annotations

import argparse
import csv
import math
import random
import subprocess
import sys
import time
from collections import Counter, defaultdict
from dataclasses import dataclass, asdict
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
EXECUTABLE = ROOT / ".lake" / "build" / "bin" / "acuihe-fuzz"


@dataclass
class Result:
    family: str
    depth: int
    seed: int
    solver: str
    status: str
    outcome: str = ""
    elapsed_ms: float | None = None
    e_ms: float | None = None
    acuih_ms: float | None = None
    wall_ms: float | None = None
    repetitions: int = 1
    configurations: float | None = None
    valid_configurations: float | None = None
    nodes: int | None = None
    additions: int | None = None
    homs: int | None = None
    es: int | None = None
    variables: int | None = None
    constants: int | None = None
    zeros: int | None = None
    syntax_depth: int | None = None
    error: str = ""


def parse_worker_output(output: str) -> dict[str, str]:
    fields: dict[str, str] = {}
    for item in output.strip().split():
        if "=" in item:
            key, value = item.split("=", 1)
            fields[key] = value
    return fields


def run_case(
    family: str,
    depth: int,
    seed: int,
    solver: str,
    shallow_bound: int,
    repetitions: int,
    timeout: float,
) -> Result:
    command = [
        str(EXECUTABLE),
        solver,
        family,
        str(seed),
        str(depth),
        str(shallow_bound),
        str(repetitions),
    ]
    started = time.perf_counter()
    try:
        completed = subprocess.run(
            command,
            cwd=ROOT,
            text=True,
            capture_output=True,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired:
        return Result(
            family=family,
            depth=depth,
            seed=seed,
            solver=solver,
            status="timeout",
            wall_ms=timeout * 1000.0,
            repetitions=repetitions,
        )
    wall_ms = (time.perf_counter() - started) * 1000.0
    if completed.returncode != 0:
        error = (completed.stderr or completed.stdout).strip().replace("\n", " ")
        return Result(
            family=family,
            depth=depth,
            seed=seed,
            solver=solver,
            status="error",
            wall_ms=wall_ms,
            repetitions=repetitions,
            error=error,
        )
    fields = parse_worker_output(completed.stdout)
    required = {"outcome", "elapsed_ms", "nodes", "syntax_depth"}
    if not required.issubset(fields):
        return Result(
            family=family,
            depth=depth,
            seed=seed,
            solver=solver,
            status="error",
            wall_ms=wall_ms,
            repetitions=repetitions,
            error=f"unparseable output: {completed.stdout.strip()}",
        )
    elapsed_ms = (
        float(fields["elapsed_ns"]) / 1_000_000.0
        if "elapsed_ns" in fields
        else float(fields["elapsed_ms"])
    )
    e_ms = (
        float(fields["e_ns"]) / 1_000_000.0 / repetitions
        if "e_ns" in fields
        else None
    )
    acuih_ms = (
        float(fields["acuih_ns"]) / 1_000_000.0 / repetitions
        if "acuih_ns" in fields
        else None
    )
    return Result(
        family=family,
        depth=depth,
        seed=seed,
        solver=solver,
        status="ok",
        outcome=fields["outcome"],
        elapsed_ms=elapsed_ms / repetitions,
        e_ms=e_ms,
        acuih_ms=acuih_ms,
        wall_ms=wall_ms / repetitions,
        repetitions=repetitions,
        configurations=(
            float(fields["configurations"]) / repetitions
            if "configurations" in fields else None
        ),
        valid_configurations=(
            float(fields["valid_configurations"]) / repetitions
            if "valid_configurations" in fields else None
        ),
        nodes=int(fields["nodes"]),
        additions=int(fields["additions"]),
        homs=int(fields["homs"]),
        es=int(fields["es"]),
        variables=int(fields["variables"]),
        constants=int(fields["constants"]),
        zeros=int(fields["zeros"]),
        syntax_depth=int(fields["syntax_depth"]),
    )


def percentile(values: list[float], probability: float) -> float:
    if not values:
        return math.nan
    ordered = sorted(values)
    location = (len(ordered) - 1) * probability
    lower = math.floor(location)
    upper = math.ceil(location)
    if lower == upper:
        return ordered[lower]
    weight = location - lower
    return ordered[lower] * (1.0 - weight) + ordered[upper] * weight


def geometric_mean(values: list[float]) -> float:
    return math.exp(sum(math.log(value) for value in values) / len(values))


def sign_test_two_sided(wins: int, losses: int) -> float:
    trials = wins + losses
    if trials == 0:
        return 1.0
    smaller = min(wins, losses)
    tail = sum(math.comb(trials, k) for k in range(smaller + 1)) / (2**trials)
    return min(1.0, 2.0 * tail)


def fmt(value: float) -> str:
    return "-" if math.isnan(value) else f"{value:.2f}"


def summarize(results: list[Result], timeout_seconds: float) -> None:
    indexed = {(r.family, r.depth, r.seed, r.solver): r for r in results}
    cases = sorted({(r.family, r.depth, r.seed) for r in results})
    paired: list[tuple[Result, Result]] = []
    mismatches: list[tuple[Result, Result]] = []
    original_timeout_optimized_ok = 0
    optimized_timeout_original_ok = 0
    for family, depth, seed in cases:
        original = indexed[(family, depth, seed, "original")]
        optimized = indexed[(family, depth, seed, "optimized")]
        if original.status == "ok" and optimized.status == "ok":
            paired.append((original, optimized))
            if original.outcome != optimized.outcome:
                mismatches.append((original, optimized))
        elif original.status == "timeout" and optimized.status == "ok":
            original_timeout_optimized_ok += 1
        elif optimized.status == "timeout" and original.status == "ok":
            optimized_timeout_original_ok += 1

    print("\nOverall")
    print(f"  generated cases: {len(cases)}")
    print(f"  completed by both: {len(paired)}")
    print(f"  classification mismatches: {len(mismatches)}")
    for solver in ("original", "optimized", "shortcut", "filo"):
        statuses = Counter(r.status for r in results if r.solver == solver)
        print(
            f"  {solver:9s}: ok={statuses['ok']} "
            f"timeout={statuses['timeout']} error={statuses['error']}"
        )
    print(
        "  original timeout / optimized complete: "
        f"{original_timeout_optimized_ok}"
    )
    print(
        "  optimized timeout / original complete: "
        f"{optimized_timeout_original_ok}"
    )

    agreed = [(old, new) for old, new in paired if old.outcome == new.outcome]
    if agreed:
        old_times = [max(old.elapsed_ms or 0.0, 0.5) for old, _ in agreed]
        new_times = [max(new.elapsed_ms or 0.0, 0.5) for _, new in agreed]
        ratios = [old / new for old, new in zip(old_times, new_times)]
        wins = sum(new < old for old, new in zip(old_times, new_times))
        losses = sum(new > old for old, new in zip(old_times, new_times))
        ties = len(agreed) - wins - losses
        print("\nPaired completed cases (solver-internal milliseconds)")
        print(
            "  original median/p90/p95: "
            f"{fmt(percentile(old_times, .5))} / "
            f"{fmt(percentile(old_times, .9))} / "
            f"{fmt(percentile(old_times, .95))}"
        )
        print(
            "  optimized median/p90/p95: "
            f"{fmt(percentile(new_times, .5))} / "
            f"{fmt(percentile(new_times, .9))} / "
            f"{fmt(percentile(new_times, .95))}"
        )
        print(f"  geometric-mean speedup: {geometric_mean(ratios):.2f}x")
        print(
            f"  optimized wins/losses/ties: {wins}/{losses}/{ties}; "
            f"two-sided sign-test p={sign_test_two_sided(wins, losses):.4g}"
        )

    grouped: dict[tuple[str, int], list[tuple[Result, Result]]] = defaultdict(list)
    for pair in agreed:
        grouped[(pair[0].family, pair[0].depth)].append(pair)
    print("\nBy distribution and requested depth")
    print(
        "  family  depth pairs sat unsat old_med_ms new_med_ms "
        "gmean_speedup old_TO new_TO"
    )
    for family, depth in sorted({(r.family, r.depth) for r in results}):
        group = grouped[(family, depth)]
        old_times = [max(old.elapsed_ms or 0.0, 0.5) for old, _ in group]
        new_times = [max(new.elapsed_ms or 0.0, 0.5) for _, new in group]
        ratios = [old / new for old, new in zip(old_times, new_times)]
        outcomes = Counter(old.outcome for old, _ in group)
        old_timeouts = sum(
            r.status == "timeout"
            for r in results
            if r.family == family and r.depth == depth and r.solver == "original"
        )
        new_timeouts = sum(
            r.status == "timeout"
            for r in results
            if r.family == family and r.depth == depth and r.solver == "optimized"
        )
        speedup = geometric_mean(ratios) if ratios else math.nan
        print(
            f"  {family:7s} {depth:5d} {len(group):5d} "
            f"{outcomes['sat']:3d} {outcomes['unsat']:5d} "
            f"{fmt(percentile(old_times, .5)):>10s} "
            f"{fmt(percentile(new_times, .5)):>10s} "
            f"{fmt(speedup):>13s} {old_timeouts:6d} {new_timeouts:6d}"
        )

    if original_timeout_optimized_ok:
        completed = [
            new
            for old, new in (
                (
                    indexed[(family, depth, seed, "original")],
                    indexed[(family, depth, seed, "optimized")],
                )
                for family, depth, seed in cases
            )
            if old.status == "timeout" and new.status == "ok"
        ]
        lower_bounds = [
            timeout_seconds * 1000.0 / max(result.elapsed_ms or 0.0, 0.5)
            for result in completed
        ]
        print(
            "\nCensored original timeouts: optimized completed these in "
            f"median {percentile([r.elapsed_ms or 0.0 for r in completed], .5):.2f} ms; "
            f"median speedup lower bound {percentile(lower_bounds, .5):.2f}x."
        )

    shortcut_pairs = []
    shortcut_mismatches = []
    for family, depth, seed in cases:
        optimized = indexed[(family, depth, seed, "optimized")]
        shortcut = indexed[(family, depth, seed, "shortcut")]
        if optimized.status == "ok" and shortcut.status == "ok":
            shortcut_pairs.append((optimized, shortcut))
            if optimized.outcome != shortcut.outcome:
                shortcut_mismatches.append((optimized, shortcut))
    shortcut_agreed = [
        pair for pair in shortcut_pairs if pair[0].outcome == pair[1].outcome
    ]
    print("\nOptimized versus shortcut")
    print(f"  completed by both: {len(shortcut_pairs)}")
    print(f"  classification mismatches: {len(shortcut_mismatches)}")
    if shortcut_agreed:
        optimized_times = [
            max(old.elapsed_ms or 0.0, 0.5) for old, _ in shortcut_agreed
        ]
        shortcut_times = [
            max(new.elapsed_ms or 0.0, 0.5) for _, new in shortcut_agreed
        ]
        ratios = [
            old / new for old, new in zip(optimized_times, shortcut_times)
        ]
        wins = sum(
            new < old for old, new in zip(optimized_times, shortcut_times)
        )
        losses = sum(
            new > old for old, new in zip(optimized_times, shortcut_times)
        )
        ties = len(shortcut_agreed) - wins - losses
        print(
            "  optimized median/p90/p95: "
            f"{fmt(percentile(optimized_times, .5))} / "
            f"{fmt(percentile(optimized_times, .9))} / "
            f"{fmt(percentile(optimized_times, .95))}"
        )
        print(
            "  shortcut  median/p90/p95: "
            f"{fmt(percentile(shortcut_times, .5))} / "
            f"{fmt(percentile(shortcut_times, .9))} / "
            f"{fmt(percentile(shortcut_times, .95))}"
        )
        print(
            "  shortcut geometric-mean speedup: "
            f"{geometric_mean(ratios):.2f}x"
        )
        print(
            f"  shortcut wins/losses/ties: {wins}/{losses}/{ties}; "
            f"two-sided sign-test p={sign_test_two_sided(wins, losses):.4g}"
        )

    filo_pairs = []
    filo_mismatches = []
    for family, depth, seed in cases:
        optimized = indexed[(family, depth, seed, "optimized")]
        filo = indexed[(family, depth, seed, "filo")]
        if optimized.status == "ok" and filo.status == "ok":
            filo_pairs.append((optimized, filo))
            if optimized.outcome != filo.outcome:
                filo_mismatches.append((optimized, filo))
    filo_agreed = [
        pair for pair in filo_pairs if pair[0].outcome == pair[1].outcome
    ]
    print("\nOptimized versus FILO")
    print(f"  completed by both: {len(filo_pairs)}")
    print(f"  classification mismatches: {len(filo_mismatches)}")
    if filo_agreed:
        optimized_times = [
            max(old.elapsed_ms or 0.0, 0.5) for old, _ in filo_agreed
        ]
        filo_times = [
            max(new.elapsed_ms or 0.0, 0.5) for _, new in filo_agreed
        ]
        ratios = [old / new for old, new in zip(optimized_times, filo_times)]
        wins = sum(new < old for old, new in zip(optimized_times, filo_times))
        losses = sum(new > old for old, new in zip(optimized_times, filo_times))
        ties = len(filo_agreed) - wins - losses
        print(
            "  optimized median/p90/p95: "
            f"{fmt(percentile(optimized_times, .5))} / "
            f"{fmt(percentile(optimized_times, .9))} / "
            f"{fmt(percentile(optimized_times, .95))}"
        )
        print(
            "  FILO      median/p90/p95: "
            f"{fmt(percentile(filo_times, .5))} / "
            f"{fmt(percentile(filo_times, .9))} / "
            f"{fmt(percentile(filo_times, .95))}"
        )
        print(f"  FILO geometric-mean speedup: {geometric_mean(ratios):.2f}x")
        print(
            f"  FILO wins/losses/ties: {wins}/{losses}/{ties}; "
            f"two-sided sign-test p={sign_test_two_sided(wins, losses):.4g}"
        )

    profiled_filo = [
        result for result in results
        if result.solver == "filo" and result.status == "ok"
        and result.e_ms is not None and result.acuih_ms is not None
    ]
    if profiled_filo:
        print("\nFILO phase attribution")
        print("  group       cases       E ms/share       ACUIh ms/share  configs/valid")
        groups = [("overall", profiled_filo)]
        groups.extend(
            (f"{family}/d{depth}", [
                result for result in profiled_filo
                if result.family == family and result.depth == depth
            ])
            for family, depth in sorted({
                (result.family, result.depth) for result in profiled_filo
            })
        )
        for label, group in groups:
            e_ms = sum(result.e_ms or 0.0 for result in group)
            acuih_ms = sum(result.acuih_ms or 0.0 for result in group)
            total_ms = e_ms + acuih_ms
            e_share = 100.0 * e_ms / total_ms if total_ms else 0.0
            acuih_share = 100.0 * acuih_ms / total_ms if total_ms else 0.0
            configurations = sum(result.configurations or 0.0 for result in group)
            valid = sum(result.valid_configurations or 0.0 for result in group)
            print(
                f"  {label:10s} {len(group):5d} "
                f"{e_ms:9.2f}/{e_share:5.1f}% "
                f"{acuih_ms:11.2f}/{acuih_share:5.1f}% "
                f"{configurations:g}/{valid:g}"
            )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=10, help="samples per family/depth")
    parser.add_argument("--depths", default="1,2,3", help="comma-separated maximum depths")
    parser.add_argument("--families", default="random,sat,cyclic")
    parser.add_argument("--seed", type=int, default=20260903)
    parser.add_argument("--timeout", type=float, default=10.0, help="seconds per solver/case")
    parser.add_argument("--shallow-bound", type=int, default=8)
    parser.add_argument("--repetitions", type=int, default=1)
    parser.add_argument("--no-build", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.samples <= 0 or args.repetitions <= 0 or args.timeout <= 0:
        parser.error("samples, repetitions, and timeout must be positive")
    depths = [int(item) for item in args.depths.split(",") if item]
    families = [item for item in args.families.split(",") if item]
    unknown = set(families) - {"random", "sat", "cyclic"}
    if unknown:
        parser.error(f"unknown families: {', '.join(sorted(unknown))}")

    if not args.no_build:
        subprocess.run(
            ["lake", "build", "acuihe-fuzz"], cwd=ROOT, check=True
        )
    if not EXECUTABLE.exists():
        parser.error(f"missing worker executable: {EXECUTABLE}")

    generator = random.Random(args.seed)
    cases = [
        (family, depth, generator.randrange(2**32))
        for family in families
        for depth in depths
        for _ in range(args.samples)
    ]
    results: list[Result] = []
    total_runs = len(cases) * 4
    completed_runs = 0
    print(
        f"Running {len(cases)} matched cases ({total_runs} processes), "
        f"timeout={args.timeout:g}s"
    )
    for case_index, (family, depth, seed) in enumerate(cases):
        solvers = ("original", "optimized", "shortcut", "filo")
        rotation = case_index % len(solvers)
        solvers = solvers[rotation:] + solvers[:rotation]
        for solver in solvers:
            result = run_case(
                family,
                depth,
                seed,
                solver,
                args.shallow_bound,
                args.repetitions,
                args.timeout,
            )
            results.append(result)
            completed_runs += 1
            print(
                f"\r  completed {completed_runs}/{total_runs}; "
                f"latest={family}/d{depth}/{solver}:{result.status}",
                end="",
                flush=True,
            )
    print()

    output = args.output
    if output is None:
        output = ROOT / "Benchmarks" / "results" / (
            f"fuzz_seed{args.seed}_n{args.samples}.csv"
        )
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(asdict(results[0]).keys()))
        writer.writeheader()
        writer.writerows(asdict(result) for result in results)
    print(f"Raw results: {output}")
    summarize(results, args.timeout)

    errors = [result for result in results if result.status == "error"]
    if errors:
        print("\nWorker errors:", file=sys.stderr)
        for result in errors[:10]:
            print(
                f"  {result.family}/d{result.depth}/{result.seed}/"
                f"{result.solver}: {result.error}",
                file=sys.stderr,
            )
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
