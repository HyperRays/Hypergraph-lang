#!/usr/bin/env python3
"""Plot matched ACUIhE fuzz results and paired statistical comparisons."""

from __future__ import annotations

import argparse
import csv
import math
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
from matplotlib.lines import Line2D


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_INPUT = ROOT / "Benchmarks" / "results" / "fuzz_shortcut_depth1_seed20260903_n10.csv"

SOLVERS = ("original", "optimized", "shortcut")
SOLVER_LABELS = {"original": "Original", "optimized": "Optimized", "shortcut": "Shortcut"}
SOLVER_COLORS = {"original": "#3465a4", "optimized": "#e07a28", "shortcut": "#2f9e62"}
FAMILIES = ("random", "sat", "cyclic")
FAMILY_LABELS = {"random": "Random", "sat": "SAT extension", "cyclic": "Cyclic"}
FAMILY_COLORS = {"random": "#8e5cc2", "sat": "#168aad", "cyclic": "#c44536"}


@dataclass(frozen=True)
class Result:
    family: str
    depth: int
    seed: int
    solver: str
    status: str
    outcome: str
    elapsed_ms: float | None


@dataclass
class Effect:
    baseline: str
    candidate: str
    family: str | None
    count: int
    estimate: float
    low: float
    high: float
    randomization_p: float
    sign_p: float
    wins: int
    losses: int
    ties: int
    holm_p: float = math.nan


def load_results(path: Path) -> list[Result]:
    with path.open(newline="") as stream:
        rows = list(csv.DictReader(stream))
    results = []
    for row in rows:
        elapsed = row.get("elapsed_ms", "")
        results.append(Result(
            family=row["family"], depth=int(row["depth"]), seed=int(row["seed"]),
            solver=row["solver"], status=row["status"], outcome=row.get("outcome", ""),
            elapsed_ms=float(elapsed) if elapsed else None,
        ))
    return results


def result_index(results: list[Result]) -> dict[tuple[str, int, int, str], Result]:
    return {(r.family, r.depth, r.seed, r.solver): r for r in results}


def matched_cases(results: list[Result]) -> list[tuple[str, int, int]]:
    return sorted({(r.family, r.depth, r.seed) for r in results})


def paired_logs(results: list[Result], baseline: str, candidate: str,
                family: str | None, timer_floor_ms: float) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    indexed = result_index(results)
    baseline_times, candidate_times = [], []
    for case in matched_cases(results):
        if family is not None and case[0] != family:
            continue
        old, new = indexed.get((*case, baseline)), indexed.get((*case, candidate))
        if old is None or new is None or old.status != "ok" or new.status != "ok":
            continue
        if old.outcome != new.outcome:
            continue
        baseline_times.append(max(old.elapsed_ms or 0.0, timer_floor_ms))
        candidate_times.append(max(new.elapsed_ms or 0.0, timer_floor_ms))
    old_array = np.asarray(baseline_times, dtype=float)
    new_array = np.asarray(candidate_times, dtype=float)
    return old_array, new_array, np.log(old_array / new_array)


def exact_sign_p(wins: int, losses: int) -> float:
    trials = wins + losses
    if trials == 0:
        return 1.0
    tail = sum(math.comb(trials, k) for k in range(min(wins, losses) + 1))
    return min(1.0, 2.0 * tail / (2**trials))


def randomization_p(log_ratios: np.ndarray, rng: np.random.Generator, samples: int) -> float:
    """Two-sided paired sign-flip test for the mean log runtime ratio."""
    if log_ratios.size == 0:
        return math.nan
    observed = abs(float(log_ratios.mean()))
    tolerance = 1e-15
    count = total = 0
    if log_ratios.size <= 20:
        total = 1 << log_ratios.size
        bit_positions = np.arange(log_ratios.size, dtype=np.uint64)
        for start in range(0, total, 16_384):
            codes = np.arange(start, min(start + 16_384, total), dtype=np.uint64)
            signs = 1.0 - 2.0 * ((codes[:, None] >> bit_positions) & 1)
            permuted = np.abs((signs * log_ratios).mean(axis=1))
            count += int(np.count_nonzero(permuted >= observed - tolerance))
        return count / total
    remaining = samples
    while remaining:
        batch = min(10_000, remaining)
        signs = rng.choice(np.asarray([-1.0, 1.0]), size=(batch, log_ratios.size))
        permuted = np.abs((signs * log_ratios).mean(axis=1))
        count += int(np.count_nonzero(permuted >= observed - tolerance))
        total += batch
        remaining -= batch
    return (count + 1) / (total + 1)


def compute_effect(results: list[Result], baseline: str, candidate: str,
                   family: str | None, timer_floor_ms: float,
                   bootstrap_samples: int, randomization_samples: int,
                   rng: np.random.Generator) -> Effect:
    old, new, log_ratios = paired_logs(results, baseline, candidate, family, timer_floor_ms)
    if log_ratios.size == 0:
        raise ValueError(f"no completed pairs for {baseline}/{candidate}/{family}")
    estimate = math.exp(float(log_ratios.mean()))
    sample_indices = rng.integers(0, log_ratios.size, size=(bootstrap_samples, log_ratios.size))
    bootstrap = np.exp(log_ratios[sample_indices].mean(axis=1))
    low, high = np.quantile(bootstrap, [0.025, 0.975])
    wins = int(np.count_nonzero(new < old))
    losses = int(np.count_nonzero(new > old))
    ties = int(log_ratios.size - wins - losses)
    return Effect(
        baseline, candidate, family, int(log_ratios.size), estimate, float(low), float(high),
        randomization_p(log_ratios, rng, randomization_samples), exact_sign_p(wins, losses),
        wins, losses, ties,
    )


def holm_adjust(effects: list[Effect]) -> None:
    ordered = sorted(enumerate(effects), key=lambda item: item[1].randomization_p)
    running, adjusted, total = 0.0, [math.nan] * len(effects), len(effects)
    for rank, (index, effect) in enumerate(ordered):
        running = max(running, min(1.0, effect.randomization_p * (total - rank)))
        adjusted[index] = running
    for effect, value in zip(effects, adjusted):
        effect.holm_p = value


def effect_label(effect: Effect) -> str:
    comparison = f"{SOLVER_LABELS[effect.baseline]} → {SOLVER_LABELS[effect.candidate]}"
    group = "Overall" if effect.family is None else FAMILY_LABELS[effect.family]
    return f"{comparison} · {group}"


def save_figure(fig: plt.Figure, base: Path) -> None:
    fig.savefig(base.with_suffix(".png"), dpi=180, bbox_inches="tight")
    fig.savefig(base.with_suffix(".svg"), bbox_inches="tight")
    plt.close(fig)


def plot_runtime_distributions(results: list[Result], output_dir: Path,
                               timeout_ms: float, timer_floor_ms: float, seed: int) -> None:
    fig, axes = plt.subplots(1, 3, figsize=(14.2, 4.8), sharey=True)
    generator = np.random.default_rng(seed)
    for axis, family in zip(axes, FAMILIES):
        family_rows = [row for row in results if row.family == family]
        for position, solver in enumerate(SOLVERS, start=1):
            rows = [row for row in family_rows if row.solver == solver]
            completed = [max(row.elapsed_ms or 0.0, timer_floor_ms)
                         for row in rows if row.status == "ok"]
            jitter = generator.uniform(-0.075, 0.075, size=len(completed))
            axis.scatter(position + jitter, completed, color=SOLVER_COLORS[solver], alpha=0.82,
                         s=31, edgecolor="white", linewidth=0.45, zorder=3)
            timeouts = sum(row.status == "timeout" for row in rows)
            if timeouts:
                axis.scatter(position + np.linspace(-0.045, 0.045, timeouts),
                             [timeout_ms] * timeouts, color=SOLVER_COLORS[solver],
                             marker="^", s=61, zorder=4)
            if completed:
                median = float(np.median(completed))
                axis.hlines(median, position - 0.20, position + 0.20,
                            color=SOLVER_COLORS[solver], linewidth=3.0, zorder=5)
                axis.annotate(f"{median:g}", (position, median), xytext=(0, 7),
                              textcoords="offset points", ha="center", va="bottom",
                              fontsize=8.5, color=SOLVER_COLORS[solver],
                              bbox={"facecolor": "white", "edgecolor": "none",
                                    "alpha": 0.72, "pad": 0.4})
        axis.set_title(FAMILY_LABELS[family])
        axis.set_xticks(range(1, 4), [SOLVER_LABELS[s] for s in SOLVERS])
        axis.set_yscale("log")
        axis.set_ylim(timer_floor_ms * 0.75, timeout_ms * 1.32)
        axis.grid(axis="y", which="both", alpha=0.22)
        axis.set_xlabel("Solver")
    axes[0].set_ylabel("Runtime (ms, logarithmic scale)")
    fig.suptitle("ACUIhE fuzzer runtime distributions", fontsize=15, y=1.02)
    fig.legend(handles=[Line2D([0], [0], marker="^", linestyle="none", color="#555555",
                               label="5 s timeout")],
               loc="upper right", bbox_to_anchor=(0.985, 1.015), frameon=False)
    fig.text(0.5, -0.015,
             "Individual runs; horizontal bars are medians. Timer readings of 0 ms are plotted at 0.5 ms.",
             ha="center", fontsize=9, color="#555555")
    fig.tight_layout()
    save_figure(fig, output_dir / "fuzz_runtime_distributions")


def plot_paired_shortcut(results: list[Result], output_dir: Path,
                         timeout_ms: float, timer_floor_ms: float,
                         shortcut_effect: Effect) -> None:
    indexed = result_index(results)
    fig, axis = plt.subplots(figsize=(7.3, 6.6))
    for family in FAMILIES:
        xs, ys, censored_x, censored_y = [], [], [], []
        for case in matched_cases(results):
            if case[0] != family:
                continue
            optimized, shortcut = indexed[(*case, "optimized")], indexed[(*case, "shortcut")]
            if optimized.status == "ok" and shortcut.status == "ok":
                xs.append(max(optimized.elapsed_ms or 0.0, timer_floor_ms))
                ys.append(max(shortcut.elapsed_ms or 0.0, timer_floor_ms))
            elif optimized.status == "timeout" or shortcut.status == "timeout":
                censored_x.append(timeout_ms if optimized.status == "timeout"
                                  else max(optimized.elapsed_ms or 0.0, timer_floor_ms))
                censored_y.append(timeout_ms if shortcut.status == "timeout"
                                  else max(shortcut.elapsed_ms or 0.0, timer_floor_ms))
        axis.scatter(xs, ys, label=FAMILY_LABELS[family], color=FAMILY_COLORS[family],
                     s=48, alpha=0.86, edgecolor="white", linewidth=0.55, zorder=3)
        if censored_x:
            axis.scatter(censored_x, censored_y, color=FAMILY_COLORS[family],
                         marker="^", s=78, zorder=4)
    limits = (timer_floor_ms * 0.75, timeout_ms * 1.3)
    axis.plot(limits, limits, linestyle="--", color="#666666", linewidth=1.1)
    axis.set_xscale("log")
    axis.set_yscale("log")
    axis.set_xlim(*limits)
    axis.set_ylim(*limits)
    axis.set_aspect("equal", adjustable="box")
    axis.grid(which="both", alpha=0.20)
    axis.set_xlabel("Optimized runtime (ms, logarithmic scale)")
    axis.set_ylabel("Shortcut runtime (ms, logarithmic scale)")
    axis.set_title("Matched optimized-versus-shortcut runtimes")
    axis.text(0.03, 0.97, "Shortcut faster", transform=axis.transAxes,
              ha="left", va="top", color="#555555")
    axis.text(0.97, 0.03, "Optimized faster", transform=axis.transAxes,
              ha="right", va="bottom", color="#555555")
    axis.text(0.03, 0.69,
              f"n = {shortcut_effect.count} completed pairs\n"
              f"GM speedup = {shortcut_effect.estimate:.2f}×\n"
              f"bootstrap 95% CI {shortcut_effect.low:.2f}–{shortcut_effect.high:.2f}\n"
              f"paired randomization p = {shortcut_effect.randomization_p:.3f}",
              transform=axis.transAxes, ha="left", va="top", fontsize=9.5,
              bbox={"boxstyle": "round,pad=0.4", "facecolor": "white",
                    "edgecolor": "#bbbbbb", "alpha": 0.90})
    axis.legend(frameon=False, loc="center left", bbox_to_anchor=(1.02, 0.5))
    fig.tight_layout()
    save_figure(fig, output_dir / "fuzz_optimized_vs_shortcut")


def plot_effects(effects: list[Effect], output_dir: Path) -> None:
    fig, axis = plt.subplots(figsize=(12.4, 7.3))
    positions = np.arange(len(effects))[::-1]
    comparison_colors = {
        ("original", "optimized"): SOLVER_COLORS["optimized"],
        ("optimized", "shortcut"): SOLVER_COLORS["shortcut"],
    }
    for position, effect in zip(positions, effects):
        color = comparison_colors[(effect.baseline, effect.candidate)]
        axis.errorbar(effect.estimate, position,
                      xerr=np.asarray([[effect.estimate - effect.low],
                                       [effect.high - effect.estimate]]),
                      fmt="o", markersize=7, capsize=4, linewidth=2.2,
                      color=color, zorder=3)
        axis.annotate(f"{effect.estimate:.2f}×", (effect.estimate, position),
                      xytext=(0, 9), textcoords="offset points", ha="center",
                      fontsize=8.5, color=color)
        significance = "*" if effect.randomization_p < 0.05 else ""
        axis.text(1.02, position,
                  f"p={effect.randomization_p:.3f}{significance}  "
                  f"Holm q={effect.holm_p:.3f}  "
                  f"W/L/T={effect.wins}/{effect.losses}/{effect.ties}",
                  transform=axis.get_yaxis_transform(), va="center", fontsize=9)
    axis.axvline(1.0, color="#666666", linestyle="--", linewidth=1.2)
    axis.set_xscale("log")
    axis.set_xlim(0.70, 3.35)
    axis.set_xticks([0.75, 1.0, 1.5, 2.0, 3.0], ["0.75×", "1×", "1.5×", "2×", "3×"])
    axis.set_yticks(positions, [effect_label(effect) for effect in effects])
    axis.grid(axis="x", which="both", alpha=0.22)
    axis.set_xlabel("Geometric-mean speedup (right is faster)")
    axis.set_title("Paired effect sizes and statistical significance", pad=13)
    axis.text(1.02, 1.025, "Raw paired test / multiple-test correction",
              transform=axis.transAxes, ha="left", va="bottom", fontsize=9, color="#555555")
    axis.legend(handles=[
        Line2D([0], [0], marker="o", color=SOLVER_COLORS["optimized"],
               label="Original → optimized"),
        Line2D([0], [0], marker="o", color=SOLVER_COLORS["shortcut"],
               label="Optimized → shortcut"),
    ], frameon=False, loc="lower right")
    fig.subplots_adjust(left=0.26, right=0.69, top=0.90, bottom=0.15)
    fig.text(0.26, 0.045,
             "Bars: paired percentile-bootstrap 95% intervals for mean log speedup. "
             "p: two-sided paired sign-flip randomization test. q: Holm correction across the eight displayed tests. "
             "Timeout pairs are excluded.",
             ha="left", fontsize=8.8, color="#555555")
    save_figure(fig, output_dir / "fuzz_statistical_significance")


def write_effects_csv(effects: list[Effect], path: Path) -> None:
    with path.open("w", newline="") as stream:
        writer = csv.writer(stream)
        writer.writerow(["baseline", "candidate", "family", "pairs",
                         "geometric_mean_speedup", "bootstrap_95_low", "bootstrap_95_high",
                         "paired_randomization_p", "holm_adjusted_p", "exact_sign_p",
                         "wins", "losses", "ties"])
        for effect in effects:
            writer.writerow([effect.baseline, effect.candidate, effect.family or "overall",
                             effect.count, effect.estimate, effect.low, effect.high,
                             effect.randomization_p, effect.holm_p, effect.sign_p,
                             effect.wins, effect.losses, effect.ties])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output-dir", type=Path,
                        default=ROOT / "Benchmarks" / "results")
    parser.add_argument("--timeout-ms", type=float, default=5000.0)
    parser.add_argument("--timer-floor-ms", type=float, default=0.5)
    parser.add_argument("--bootstrap-samples", type=int, default=20_000)
    parser.add_argument("--randomization-samples", type=int, default=200_000)
    parser.add_argument("--seed", type=int, default=20260903)
    args = parser.parse_args()
    if args.timeout_ms <= 0 or args.timer_floor_ms <= 0:
        parser.error("timeout and timer floor must be positive")
    if args.bootstrap_samples <= 0 or args.randomization_samples <= 0:
        parser.error("sample counts must be positive")

    results = load_results(args.input)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    rng = np.random.default_rng(args.seed)
    effects = [
        compute_effect(results, baseline, candidate, family, args.timer_floor_ms,
                       args.bootstrap_samples, args.randomization_samples, rng)
        for baseline, candidate in (("original", "optimized"), ("optimized", "shortcut"))
        for family in (None, *FAMILIES)
    ]
    holm_adjust(effects)

    plot_runtime_distributions(results, args.output_dir, args.timeout_ms,
                               args.timer_floor_ms, args.seed)
    shortcut_overall = next(effect for effect in effects
                            if effect.baseline == "optimized"
                            and effect.candidate == "shortcut"
                            and effect.family is None)
    plot_paired_shortcut(results, args.output_dir, args.timeout_ms,
                         args.timer_floor_ms, shortcut_overall)
    plot_effects(effects, args.output_dir)
    write_effects_csv(effects, args.output_dir / "fuzz_statistical_summary.csv")

    print(f"Input: {args.input}")
    print(f"Cases: {len(matched_cases(results))}")
    for solver in SOLVERS:
        statuses = Counter(r.status for r in results if r.solver == solver)
        print(f"{solver}: ok={statuses['ok']} timeout={statuses['timeout']} error={statuses['error']}")
    for effect in effects:
        print(f"{effect_label(effect)}: {effect.estimate:.3f}x "
              f"[{effect.low:.3f}, {effect.high:.3f}], "
              f"p={effect.randomization_p:.4g}, Holm q={effect.holm_p:.4g}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
