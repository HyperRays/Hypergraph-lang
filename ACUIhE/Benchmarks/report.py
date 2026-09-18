#!/usr/bin/env python3
"""Render retained observations; no solver calls or missing-time imputation."""

import argparse
import collections
import json
from pathlib import Path
import random
import statistics


def read(directory):
    cases = {c["id"]: c for c in map(json.loads, (directory/"cases.jsonl").read_text().splitlines())}
    runs = [dict(cases[r["id"]], **r) for r in map(json.loads, (directory/"runs.jsonl").read_text().splitlines())]
    return json.loads((directory/"metadata.json").read_text()), runs


def ms(x):
    return "—" if x is None else f"{x:.3f}"


def table(rows, keys):
    groups = collections.defaultdict(list)
    for r in rows:
        groups[tuple(r[k] for k in keys)].append(r)
    lines = ["| " + " | ".join(keys) + " | n | completed | median ms, completed only | median nodes | median E count |",
             "|" + "---|" * (len(keys)+5)]
    for key, group in sorted(groups.items()):
        complete = [r for r in group if r["status"] == "ok"]
        elapsed = [r["elapsed_ns"]/1e6 for r in complete]
        lines.append("| " + " | ".join(map(str, key)) +
                     f" | {len(group)} | {len(complete)}/{len(group)} ({len(complete)/len(group):.1%})" +
                     f" | {ms(statistics.median(elapsed) if elapsed else None)}" +
                     f" | {statistics.median(r['nodes'] for r in group):g}" +
                     f" | {statistics.median(r['e_count'] for r in group):g} |")
    return lines


def paired(rows):
    groups = collections.defaultdict(lambda: collections.defaultdict(list))
    for r in rows:
        groups[r["id"]][r["mode"]].append(r)
    ratios = []
    weights = []
    complete_d = complete_w = lost_w = 0
    for modes in groups.values():
        d, w = modes["decision"], modes["witness"]
        dc = bool(d) and all(r["status"] == "ok" for r in d)
        wc = bool(w) and all(r["status"] == "ok" for r in w)
        complete_d += dc
        complete_w += wc
        lost_w += dc and not wc
        if wc:
            weights.append(w[0]["graph_weight"])
            if len({r["graph_weight"] for r in w}) != 1:
                raise ValueError("repeated pure solver output weights differ")
        if dc and wc:
            ratios.append(statistics.median(r["elapsed_ns"] for r in w)/
                          statistics.median(r["elapsed_ns"] for r in d))
    lines = [f"{len(groups)} planted-SAT inputs, with three fresh-process repetitions per mode.", "",
             f"All repetitions completed: decision {complete_d}/{len(groups)}; "
             f"extracted witness {complete_w}/{len(groups)}. "
             f"{lost_w} inputs completed in every decision run but timed out in at least one witness run."]
    if ratios:
        rng = random.Random(20260910)
        boots = sorted(statistics.median(rng.choices(ratios, k=len(ratios))) for _ in range(5000))
        lines += ["", f"For the {len(ratios)} fully observed input pairs, the median ratio of "
                  f"per-input median witness/decision times was {statistics.median(ratios):.2f}× "
                  f"(input-bootstrap 95% interval {boots[124]:.2f}–{boots[4874]:.2f}×). "
                  "This ratio is conditional on completion in both modes; it does not summarize censored inputs."]
    if weights:
        lines += ["", f"Completed witnesses are small in this cohort: {sum(w == 0 for w in weights)} "
                  f"have zero total graph weight; median weight {statistics.median(weights):g}, "
                  f"maximum {max(weights)}. Weight counts canonical summands, E edges and word lengths "
                  "across queried variables. This cohort does not exercise worst-case large-output expansion."]
    return lines


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--decision", type=Path, required=True)
    p.add_argument("--paired", type=Path)
    p.add_argument("--extended", type=Path)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    metadata, rows = read(args.decision)
    complete = [r for r in rows if r["status"] == "ok"]
    known = [r for r in complete if r["expected"] is not None]
    timeout = metadata["arguments"]["timeout"]
    lines = ["# ACUIhE grammar-fuzz performance results", "",
             f"Run date: {metadata['timestamp_utc']}. Platform: {metadata['platform']}, "
             f"{metadata['machine']}, {metadata['cpu_count']} logical CPUs. "
             f"Toolchain: `{metadata['lean_toolchain']}`.", "",
             "## Scope and interpretation", "",
             "Every observation uses the full solver, including h-only and E-only inputs. "
             "These are synthetic distributions, not a uniform sample of algebraic problems or a complexity proof. "
             "See [methodology](../README.md) for the grammar, independently justified labels, timing protocol, "
             "and statistical limitations.", "",
             f"The primary run contains {len(rows)} independently seeded input measurements, with "
             f"a {timeout:g}-second post-handshake wall cutoff. "
             f"{len(complete)} completed; {sum(r['status']=='timeout' for r in rows)} timed out. "
             f"Worker errors: {sum(r['status']=='error' for r in rows)}. "
             f"Known-label disagreements: {sum(r['status']=='mismatch' for r in rows)} "
             f"across {len(known)} completed independently labelled cases.", "",
             "The reported millisecond medians are **conditional on completion**. "
             "They must be read with the completion rates: they omit the censored slow tail. "
             "Timeouts are not negative answers. Table rows pool deliberately balanced size/equation-count strata; "
             "they do not estimate performance for an unspecified real-world workload.", "",
             "## Primary run: grammar profile and population", ""]
    lines += table(rows, ["profile", "family"])
    lines += ["", "`h` and `E` describe allowed operators, not alternative solver implementations. "
              "The third constant is reserved for UNSAT certificates. "
              "SAT samples use a shared planted substitution, and the random population has no planted label.", "",
              "## Full mixed-grammar input sizes", "",
              "`budget` is per seed term, not total syntax size. The actual node and E counts include all "
              "equations and both sides. Systems are solved simultaneously, not one equation at a time.", ""]
    lines += table([r for r in rows if r["profile"] == "mixed"], ["budget", "equations", "family"])
    lines += ["", "## Structural association with E occurrences", "",
              "This is descriptive, not a controlled causal comparison: grammar, labels, variables and "
              "problem size also change between bins.", ""]
    for r in rows:
        e = r["e_count"]
        r["E bin"] = "0" if e == 0 else "1–2" if e <= 2 else "3–4" if e <= 4 else "5–6" if e <= 6 else "7+"
    lines += table(rows, ["E bin", "family"])
    summary_path = args.decision / "summary.json"
    if summary_path.exists():
        summaries = json.loads(summary_path.read_text())
        lines += ["", "## Pointwise uncertainty for mixed-grammar cells", "",
                  "Completion intervals are Wilson 95% intervals over independent inputs. "
                  "Capped wall-cost intervals are input-bootstrap 95% intervals (2,000 resamples). "
                  "Capped wall cost includes post-handshake communication/exit overhead and stops at the cutoff; "
                  "it is not the internal solver time or the uncensored mean.", "",
                  "| budget | equations | family | completion %, 95% interval | mean capped wall ms, 95% interval |",
                  "|---|---|---|---|---|"]
        for s in summaries:
            if s["profile"] != "mixed":
                continue
            lo, hi = s["completion_ci95"]
            clo, chi = s["capped_wall_ci95_ms"]
            lines.append(f"| {s['budget']} | {s['equations']} | {s['family']} | "
                         f"{100*s['all_repeats_complete']/s['samples']:.0f}% [{100*lo:.1f}, {100*hi:.1f}] | "
                         f"{s['capped_wall_mean_ms']:.1f} [{clo:.1f}, {chi:.1f}] |")
    lines += ["", "## Unconditioned random answers", ""]
    for profile in ("h", "E", "mixed"):
        rr = [r for r in rows if r["profile"] == profile and r["family"] == "random"]
        yes = sum(r["status"] == "ok" and r["answer"] for r in rr)
        no = sum(r["status"] == "ok" and not r["answer"] for r in rr)
        unknown = sum(r["status"] == "timeout" for r in rr)
        lines.append(f"- {profile}: {yes} SAT, {no} UNSAT, {unknown} unknown at cutoff (n={len(rr)}).")
    if args.extended:
        emeta, extended = read(args.extended)
        lines += ["", "## Longer-cutoff mixed-grammar follow-up", "",
                  f"A fixed subset (the first sample indices, not selected by observed difficulty) was "
                  f"rerun at {emeta['arguments']['timeout']:g} seconds. "
                  "These inputs overlap the primary run and are not additional independent samples.", ""]
        primary = {r["id"]: r for r in rows}
        rescued = sum(primary[r["id"]]["status"] == "timeout" and r["status"] == "ok" for r in extended)
        remaining = sum(r["status"] == "timeout" for r in extended)
        regressed = sum(primary[r["id"]]["status"] == "ok" and r["status"] == "timeout" for r in extended)
        lines += [f"Of {len(extended)} rerun inputs, {rescued} primary timeouts completed, "
                  f"{remaining} remained censored, and {regressed} formerly completed inputs timed out.", ""]
        lines += table(extended, ["budget", "family"])
    if args.paired:
        _, pp = read(args.paired)
        lines += ["", "## Decision versus extracted witness", ""] + paired(pp)
    lines += ["", "## Reproducibility and uncertainty", "",
              "Each run directory contains `cases.jsonl`, `runs.jsonl`, `metadata.json`, and `summary.json`. "
              "The last file gives every sampling cell separately, with Wilson completion intervals and "
              "input-clustered bootstrap intervals for mean capped wall cost. These are pointwise 95% intervals, "
              "not simultaneous claims across all cells. Repetitions are not counted as independent inputs.", "",
              "The capped cost estimates E[min(T, cutoff)], not uncensored mean runtime. "
              "Unrestricted mean runtime and high percentiles beyond the censoring threshold are not identifiable "
              "from this experiment. No asymptotic exponent was fitted to these small, differently shaped inputs.", "",
              "Compilation, generation, parsing and startup are excluded from internal solver times. "
              "Fresh processes run serially in shuffled order. Memory is not measured because the macOS "
              "RSS collection command is blocked by the sandbox. Frequency, thermal state and unrelated host "
              "activity are uncontrolled. Pilot observations are excluded from the primary statistics.", "",
              f"Primary executable SHA-256: `{metadata['executable_sha256']}`.", "",
              f"Primary source SHA-256: `{metadata['source_sha256']}`.", ""]
    args.output.write_text("\n".join(lines))
    print(args.output)


if __name__ == "__main__":
    main()
