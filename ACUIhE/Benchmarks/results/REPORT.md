# ACUIhE grammar-fuzz performance results

Run date: 2026-09-10T00:34:04.104589+00:00. Platform: macOS-26.6.2-arm64-arm-64bit, arm64, 8 logical CPUs. Toolchain: `leanprover/lean4:v4.33.1`.

## Scope and interpretation

Every observation uses the full solver, including h-only and E-only inputs. These are synthetic distributions, not a uniform sample of algebraic problems or a complexity proof. See [methodology](../README.md) for the grammar, independently justified labels, timing protocol, and statistical limitations.

The primary run contains 1080 independently seeded input measurements, with a 0.5-second post-handshake wall cutoff. 641 completed; 439 timed out. Worker errors: 0. Known-label disagreements: 0 across 437 completed independently labelled cases.

The reported millisecond medians are **conditional on completion**. They must be read with the completion rates: they omit the censored slow tail. Timeouts are not negative answers. Table rows pool deliberately balanced size/equation-count strata; they do not estimate performance for an unspecified real-world workload.

## Primary run: grammar profile and population

| profile | family | n | completed | median ms, completed only | median nodes | median E count |
|---|---|---|---|---|---|---|
| E | random | 120 | 45/120 (37.5%) | 2.440 | 16 | 4 |
| E | sat | 120 | 50/120 (41.7%) | 0.190 | 19 | 4 |
| E | unsat | 120 | 34/120 (28.3%) | 0.491 | 16 | 4 |
| h | random | 120 | 102/120 (85.0%) | 1.304 | 16 | 0 |
| h | sat | 120 | 105/120 (87.5%) | 0.710 | 18 | 0 |
| h | unsat | 120 | 114/120 (95.0%) | 0.574 | 16 | 0 |
| mixed | random | 120 | 57/120 (47.5%) | 1.536 | 16 | 3 |
| mixed | sat | 120 | 66/120 (55.0%) | 3.619 | 18 | 4 |
| mixed | unsat | 120 | 68/120 (56.7%) | 4.146 | 16 | 2 |

`h` and `E` describe allowed operators, not alternative solver implementations. The third constant is reserved for UNSAT certificates. SAT samples use a shared planted substitution, and the random population has no planted label.

## Full mixed-grammar input sizes

`budget` is per seed term, not total syntax size. The actual node and E counts include all equations and both sides. Systems are solved simultaneously, not one equation at a time.

| budget | equations | family | n | completed | median ms, completed only | median nodes | median E count |
|---|---|---|---|---|---|---|---|
| 3 | 1 | random | 20 | 20/20 (100.0%) | 0.326 | 6 | 1 |
| 3 | 1 | sat | 20 | 15/20 (75.0%) | 0.067 | 7 | 0 |
| 3 | 1 | unsat | 20 | 14/20 (70.0%) | 2.643 | 8.5 | 1 |
| 3 | 3 | random | 20 | 9/20 (45.0%) | 21.868 | 18 | 3.5 |
| 3 | 3 | sat | 20 | 11/20 (55.0%) | 6.597 | 21 | 4 |
| 3 | 3 | unsat | 20 | 15/20 (75.0%) | 0.537 | 12 | 1.5 |
| 5 | 1 | random | 20 | 18/20 (90.0%) | 3.623 | 10 | 2 |
| 5 | 1 | sat | 20 | 18/20 (90.0%) | 2.418 | 12 | 2 |
| 5 | 1 | unsat | 20 | 13/20 (65.0%) | 0.341 | 14 | 2 |
| 5 | 3 | random | 20 | 0/20 (0.0%) | — | 30 | 5.5 |
| 5 | 3 | sat | 20 | 7/20 (35.0%) | 31.947 | 34 | 5 |
| 5 | 3 | unsat | 20 | 13/20 (65.0%) | 11.580 | 17 | 2 |
| 7 | 1 | random | 20 | 10/20 (50.0%) | 18.320 | 14 | 3 |
| 7 | 1 | sat | 20 | 12/20 (60.0%) | 10.335 | 16 | 2 |
| 7 | 1 | unsat | 20 | 9/20 (45.0%) | 4.290 | 18.5 | 2.5 |
| 7 | 3 | random | 20 | 0/20 (0.0%) | — | 42 | 8 |
| 7 | 3 | sat | 20 | 3/20 (15.0%) | 86.908 | 50 | 8 |
| 7 | 3 | unsat | 20 | 4/20 (20.0%) | 3.180 | 22 | 4.5 |

## Structural association with E occurrences

This is descriptive, not a controlled causal comparison: grammar, labels, variables and problem size also change between bins.

| E bin | family | n | completed | median ms, completed only | median nodes | median E count |
|---|---|---|---|---|---|---|
| 0 | random | 142 | 124/142 (87.3%) | 0.594 | 14 | 0 |
| 0 | sat | 171 | 155/171 (90.6%) | 0.255 | 16 | 0 |
| 0 | unsat | 174 | 168/174 (96.6%) | 0.327 | 15 | 0 |
| 1–2 | random | 64 | 58/64 (90.6%) | 5.873 | 10 | 2 |
| 1–2 | sat | 38 | 35/38 (92.1%) | 5.635 | 14 | 2 |
| 1–2 | unsat | 51 | 44/51 (86.3%) | 11.145 | 14 | 2 |
| 3–4 | random | 60 | 16/60 (26.7%) | 51.080 | 14 | 4 |
| 3–4 | sat | 52 | 18/52 (34.6%) | 11.604 | 16 | 4 |
| 3–4 | unsat | 72 | 4/72 (5.6%) | 400.527 | 15.5 | 4 |
| 5–6 | random | 33 | 4/33 (12.1%) | 0.052 | 18 | 6 |
| 5–6 | sat | 26 | 3/26 (11.5%) | 86.908 | 19.5 | 6 |
| 5–6 | unsat | 32 | 0/32 (0.0%) | — | 18.5 | 5 |
| 7+ | random | 61 | 2/61 (3.3%) | 0.078 | 42 | 10 |
| 7+ | sat | 73 | 10/73 (13.7%) | 29.117 | 36 | 8 |
| 7+ | unsat | 31 | 0/31 (0.0%) | — | 20 | 8 |

## Pointwise uncertainty for mixed-grammar cells

Completion intervals are Wilson 95% intervals over independent inputs. Capped wall-cost intervals are input-bootstrap 95% intervals (2,000 resamples). Capped wall cost includes post-handshake communication/exit overhead and stops at the cutoff; it is not the internal solver time or the uncensored mean.

| budget | equations | family | completion %, 95% interval | mean capped wall ms, 95% interval |
|---|---|---|---|---|
| 3 | 1 | random | 100% [83.9, 100.0] | 5.9 [1.4, 12.3] |
| 3 | 1 | sat | 75% [53.1, 88.8] | 126.1 [27.2, 225.9] |
| 3 | 1 | unsat | 70% [48.1, 85.5] | 154.6 [55.4, 253.6] |
| 3 | 3 | random | 45% [25.8, 65.8] | 304.6 [199.6, 404.2] |
| 3 | 3 | sat | 55% [34.2, 74.2] | 234.7 [131.5, 337.3] |
| 3 | 3 | unsat | 75% [53.1, 88.8] | 132.0 [52.3, 230.8] |
| 5 | 1 | random | 90% [69.9, 97.2] | 107.6 [35.2, 197.8] |
| 5 | 1 | sat | 90% [69.9, 97.2] | 55.6 [4.8, 130.0] |
| 5 | 1 | unsat | 65% [43.3, 81.9] | 202.5 [106.5, 297.0] |
| 5 | 3 | random | 0% [0.0, 16.1] | 500.0 [500.0, 500.0] |
| 5 | 3 | sat | 35% [18.1, 56.7] | 341.2 [244.1, 433.7] |
| 5 | 3 | unsat | 65% [43.3, 81.9] | 203.7 [106.0, 304.3] |
| 7 | 1 | random | 50% [29.9, 70.1] | 300.1 [200.4, 398.1] |
| 7 | 1 | sat | 60% [38.7, 78.1] | 224.1 [124.8, 316.1] |
| 7 | 1 | unsat | 45% [25.8, 65.8] | 291.9 [182.1, 391.1] |
| 7 | 3 | random | 0% [0.0, 16.1] | 500.0 [500.0, 500.0] |
| 7 | 3 | sat | 15% [5.2, 36.0] | 452.9 [388.4, 500.0] |
| 7 | 3 | unsat | 20% [8.1, 41.6] | 419.2 [338.3, 493.8] |

## Unconditioned random answers

- h: 27 SAT, 75 UNSAT, 18 unknown at cutoff (n=120).
- E: 18 SAT, 27 UNSAT, 75 unknown at cutoff (n=120).
- mixed: 26 SAT, 31 UNSAT, 63 unknown at cutoff (n=120).

## Longer-cutoff mixed-grammar follow-up

A fixed subset (the first sample indices, not selected by observed difficulty) was rerun at 3 seconds. These inputs overlap the primary run and are not additional independent samples.

Of 90 rerun inputs, 7 primary timeouts completed, 36 remained censored, and 0 formerly completed inputs timed out.

| budget | family | n | completed | median ms, completed only | median nodes | median E count |
|---|---|---|---|---|---|---|
| 3 | random | 10 | 7/10 (70.0%) | 1.528 | 12 | 2 |
| 3 | sat | 10 | 10/10 (100.0%) | 5.289 | 13 | 2 |
| 3 | unsat | 10 | 10/10 (100.0%) | 2.962 | 10.5 | 0.5 |
| 5 | random | 10 | 5/10 (50.0%) | 22.565 | 20 | 2.5 |
| 5 | sat | 10 | 5/10 (50.0%) | 1.072 | 22.5 | 4.5 |
| 5 | unsat | 10 | 5/10 (50.0%) | 1.224 | 16.5 | 3 |
| 7 | random | 10 | 3/10 (30.0%) | 7.512 | 28 | 4.5 |
| 7 | sat | 10 | 5/10 (50.0%) | 86.694 | 32 | 5 |
| 7 | unsat | 10 | 4/10 (40.0%) | 143.929 | 21 | 3.5 |

## Decision versus extracted witness

60 planted-SAT inputs, with three fresh-process repetitions per mode.

All repetitions completed: decision 39/60; extracted witness 39/60. 0 inputs completed in every decision run but timed out in at least one witness run.

For the 39 fully observed input pairs, the median ratio of per-input median witness/decision times was 1.18× (input-bootstrap 95% interval 1.05–1.28×). This ratio is conditional on completion in both modes; it does not summarize censored inputs.

Completed witnesses are small in this cohort: 16 have zero total graph weight; median weight 1, maximum 3. Weight counts canonical summands, E edges and word lengths across queried variables. This cohort does not exercise worst-case large-output expansion.

## Reproducibility and uncertainty

Each run directory contains `cases.jsonl`, `runs.jsonl`, `metadata.json`, and `summary.json`. The last file gives every sampling cell separately, with Wilson completion intervals and input-clustered bootstrap intervals for mean capped wall cost. These are pointwise 95% intervals, not simultaneous claims across all cells. Repetitions are not counted as independent inputs.

The capped cost estimates E[min(T, cutoff)], not uncensored mean runtime. Unrestricted mean runtime and high percentiles beyond the censoring threshold are not identifiable from this experiment. No asymptotic exponent was fitted to these small, differently shaped inputs.

Compilation, generation, parsing and startup are excluded from internal solver times. Fresh processes run serially in shuffled order. Memory is not measured because the macOS RSS collection command is blocked by the sandbox. Frequency, thermal state and unrelated host activity are uncontrolled. Pilot observations are excluded from the primary statistics.

Primary executable SHA-256: `65f7d72461641021296cee7011cbf2daa4717f4b463c38dea20b1b536f09a309`.

Primary source SHA-256: `0b5cbe2ba29a78a08d6d37ef2d134693d5b6b46548aabf8a744787bc4f3354a0`.
