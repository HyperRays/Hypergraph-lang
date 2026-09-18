#!/usr/bin/env python3
"""Report a longer-cutoff replay of precisely the previous decision timeouts."""

import argparse
import collections
import os
from pathlib import Path
import statistics

from compare import read


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--primary", type=Path, required=True)
    parser.add_argument("--followup", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    pm, pc, pr = read(args.primary)
    fm, fc, fr = read(args.followup)
    for meta in (pm, fm):
        if meta["arguments"]["modes"] != ["decision"] or meta["arguments"]["repeats"] != 1:
            raise ValueError("Expected one decision run per input")
    previous = {key[0]: run for key, run in pr.items()}
    followup = {key[0]: run for key, run in fr.items()}
    expected = {key: case for key, case in pc.items() if previous[key]["status"] == "timeout"}
    if fc != expected:
        raise ValueError("Follow-up must replay precisely the primary timeouts without changing inputs")
    if pm["executable_sha256"] != fm["executable_sha256"]:
        raise ValueError("Executable changed between measurement stages")
    old_cutoff, cutoff = (m["arguments"]["timeout"] for m in (pm, fm))
    if cutoff <= old_cutoff:
        raise ValueError("Follow-up cutoff must be longer")
    for cases, runs in ((pc, previous), (fc, followup)):
        for key, run in runs.items():
            if (run["status"] == "ok" and cases[key]["expected"] is not None
                    and run["answer"] != cases[key]["expected"]):
                raise ValueError(f"Known-answer disagreement: {key}")
    old_ok = sum(r["status"] == "ok" for r in previous.values())
    completed = [r for r in followup.values() if r["status"] == "ok"]
    remaining = [key for key, r in followup.items() if r["status"] == "timeout"]
    labelled = sum(fc[r["id"]]["expected"] is not None for r in completed)
    lines = ["# Longer-cutoff follow-up of the shared E-rule solver", "",
             f"The primary experiment completed {old_ok}/{len(pc)} inputs at a {old_cutoff:g}-second "
             f"deadline. All {len(fc)} timeouts were replayed, without changing their inputs, "
             f"at {cutoff:g} seconds per input. The compiled executable is identical.", "",
             f"The follow-up completed **{len(completed)}/{len(fc)}** previously timed-out inputs. "
             f"This brings cumulative completion to **{old_ok + len(completed)}/{len(pc)} "
             f"({(old_ok + len(completed))/len(pc):.1%})**. **{len(remaining)}** inputs remain censored "
             f"at {cutoff:g} seconds. Worker errors and known-answer disagreements: zero "
             f"({labelled} independently labelled follow-up completions).", "",
             "## Interpretation", "",
             "This is a conditional follow-up of the slow tail, not a new random sample. "
             "The earlier completed inputs were not rerun. Cumulative totals combine their recorded "
             "answers with the follow-up; they are not a fresh whole-cohort measurement at the new "
             "deadline. A timeout remains unknown and is never counted as an UNSAT answer. "
             "These are decision measurements, not witness-extraction measurements.", "",
             "Startup and parsing are outside the timed region. Fresh processes run serially in "
             "shuffled order, with the same timing protocol as the primary experiment. "
             "The deadline covers post-handshake wall time; internal solver time excludes communication "
             "and exit overhead. Host load and thermal state are uncontrolled. Results do not extrapolate "
             "to longer cutoffs, larger inputs, or arbitrary workloads.", "",
             "## Completion by grammar", "",
             "| profile | primary completed | newly completed | cumulative completed | still timed out |",
             "|---|---|---|---|---|"]
    for profile in ("h", "E", "mixed"):
        ids = [key for key, c in pc.items() if c["profile"] == profile]
        if not ids:
            continue
        before = sum(previous[key]["status"] == "ok" for key in ids)
        added = sum(key in followup and followup[key]["status"] == "ok" for key in ids)
        lines.append(f"| {profile} | {before}/{len(ids)} | {added} | {before+added}/{len(ids)} | {len(ids)-before-added} |")
    lines += ["", "## Observed cumulative completion versus budget", "",
              "Intermediate budgets are read from the follow-up's successful wall times; they were "
              "not separate reruns. Earlier primary completions are carried forward. At the actual "
              "deadlines, completion uses the supervisor's recorded status.", "",
              "| per-input budget, seconds | cumulative completed | percentage |",
              "|---|---|---|"]
    thresholds = sorted({old_cutoff, cutoff} | {t for t in (1, 3, 5, 10, 30, 60) if old_cutoff < t < cutoff})
    for threshold in thresholds:
        extra = 0 if threshold == old_cutoff else sum(
            threshold == cutoff or r["wall_s"] <= threshold for r in completed)
        total = old_ok + extra
        lines.append(f"| {threshold:g} | {total}/{len(pc)} | {total/len(pc):.1%} |")
    if completed:
        elapsed = [r["elapsed_ns"] / 1e9 for r in completed]
        lines += ["", f"Among the {len(completed)} follow-up completions only, internal solver time "
                  f"ranged from {min(elapsed):.3f} to {max(elapsed):.3f} seconds, "
                  f"with median {statistics.median(elapsed):.3f} seconds. "
                  "This conditional median omits all remaining timeouts."]
    lines += ["", "## Follow-up answers and remaining cases", "",
              "| input family | newly completed SAT | newly completed UNSAT | remaining timeouts |",
              "|---|---|---|---|"]
    for family in ("sat", "unsat", "random"):
        rr = [r for r in followup.values() if fc[r["id"]]["family"] == family]
        counts = collections.Counter("timeout" if r["status"] == "timeout" else
                                     "sat" if r["answer"] else "unsat" for r in rr)
        lines.append(f"| {family} | {counts['sat']} | {counts['unsat']} | {counts['timeout']} |")
    lines += ["", "Remaining input IDs (complete equations and their metadata are retained in `cases.jsonl`):", ""]
    lines += [f"- `{key}`" for key in sorted(remaining)] or ["None."]
    lines += ["", "## Provenance", "",
              f"Primary run: {pm['timestamp_utc']}; follow-up: {fm['timestamp_utc']}.", "",
              f"Raw data: [primary]({os.path.relpath(args.primary, args.output.parent)}), "
              f"[follow-up]({os.path.relpath(args.followup, args.output.parent)}). "
              "See [benchmark methodology](../README.md) for reproduction commands.", "",
              f"Executable SHA-256 (both stages): `{fm['executable_sha256']}`.", ""]
    args.output.write_text("\n".join(lines))
    print(args.output)


if __name__ == "__main__":
    main()
