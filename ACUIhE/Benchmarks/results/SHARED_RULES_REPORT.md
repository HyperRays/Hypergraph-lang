# ACUIhE grammar-fuzz performance results

Run date: 2026-09-10T02:07:30.485855+00:00. Platform: macOS-26.6.2-arm64-arm-64bit, arm64, 8 logical CPUs. Toolchain: `leanprover/lean4:v4.33.1`.

## Scope and interpretation

Every observation uses the full solver, including h-only and E-only inputs. These are synthetic distributions, not a uniform sample of algebraic problems or a complexity proof. See [methodology](../README.md) for the grammar, independently justified labels, timing protocol, and statistical limitations.

The primary run contains 1080 independently seeded input measurements, with a 0.5-second post-handshake wall cutoff. 966 completed; 114 timed out. Worker errors: 0. Known-label disagreements: 0 across 652 completed independently labelled cases.

The reported millisecond medians are **conditional on completion**. They must be read with the completion rates: they omit the censored slow tail. Timeouts are not negative answers. Table rows pool deliberately balanced size/equation-count strata; they do not estimate performance for an unspecified real-world workload.

## Primary run: grammar profile and population

| profile | family | n | completed | median ms, completed only | median nodes | median E count |
|---|---|---|---|---|---|---|
| E | random | 120 | 104/120 (86.7%) | 1.567 | 16 | 4 |
| E | sat | 120 | 97/120 (80.8%) | 2.031 | 19 | 4 |
| E | unsat | 120 | 117/120 (97.5%) | 1.411 | 16 | 4 |
| h | random | 120 | 112/120 (93.3%) | 0.733 | 16 | 0 |
| h | sat | 120 | 108/120 (90.0%) | 0.534 | 18 | 0 |
| h | unsat | 120 | 118/120 (98.3%) | 0.169 | 16 | 0 |
| mixed | random | 120 | 98/120 (81.7%) | 3.187 | 16 | 3 |
| mixed | sat | 120 | 94/120 (78.3%) | 2.389 | 18 | 4 |
| mixed | unsat | 120 | 118/120 (98.3%) | 0.751 | 16 | 2 |

`h` and `E` describe allowed operators, not alternative solver implementations. The third constant is reserved for UNSAT certificates. SAT samples use a shared planted substitution, and the random population has no planted label.

## Full mixed-grammar input sizes

`budget` is per seed term, not total syntax size. The actual node and E counts include all equations and both sides. Systems are solved simultaneously, not one equation at a time.

| budget | equations | family | n | completed | median ms, completed only | median nodes | median E count |
|---|---|---|---|---|---|---|---|
| 3 | 1 | random | 20 | 20/20 (100.0%) | 0.148 | 6 | 1 |
| 3 | 1 | sat | 20 | 20/20 (100.0%) | 0.314 | 7 | 0 |
| 3 | 1 | unsat | 20 | 20/20 (100.0%) | 0.193 | 8.5 | 1 |
| 3 | 3 | random | 20 | 20/20 (100.0%) | 5.813 | 18 | 3.5 |
| 3 | 3 | sat | 20 | 17/20 (85.0%) | 3.565 | 21 | 4 |
| 3 | 3 | unsat | 20 | 20/20 (100.0%) | 0.344 | 12 | 1.5 |
| 5 | 1 | random | 20 | 20/20 (100.0%) | 0.878 | 10 | 2 |
| 5 | 1 | sat | 20 | 19/20 (95.0%) | 0.299 | 12 | 2 |
| 5 | 1 | unsat | 20 | 20/20 (100.0%) | 0.289 | 14 | 2 |
| 5 | 3 | random | 20 | 13/20 (65.0%) | 57.880 | 30 | 5.5 |
| 5 | 3 | sat | 20 | 15/20 (75.0%) | 18.443 | 34 | 5 |
| 5 | 3 | unsat | 20 | 20/20 (100.0%) | 1.237 | 17 | 2 |
| 7 | 1 | random | 20 | 19/20 (95.0%) | 4.345 | 14 | 3 |
| 7 | 1 | sat | 20 | 17/20 (85.0%) | 2.891 | 16 | 2 |
| 7 | 1 | unsat | 20 | 20/20 (100.0%) | 1.013 | 18.5 | 2.5 |
| 7 | 3 | random | 20 | 6/20 (30.0%) | 107.731 | 42 | 8 |
| 7 | 3 | sat | 20 | 6/20 (30.0%) | 72.819 | 50 | 8 |
| 7 | 3 | unsat | 20 | 18/20 (90.0%) | 4.424 | 22 | 4.5 |

## Structural association with E occurrences

This is descriptive, not a controlled causal comparison: grammar, labels, variables and problem size also change between bins.

| E bin | family | n | completed | median ms, completed only | median nodes | median E count |
|---|---|---|---|---|---|---|
| 0 | random | 142 | 134/142 (94.4%) | 0.483 | 14 | 0 |
| 0 | sat | 171 | 158/171 (92.4%) | 0.189 | 16 | 0 |
| 0 | unsat | 174 | 172/174 (98.9%) | 0.139 | 15 | 0 |
| 1–2 | random | 64 | 63/64 (98.4%) | 0.399 | 10 | 2 |
| 1–2 | sat | 38 | 37/38 (97.4%) | 1.032 | 14 | 2 |
| 1–2 | unsat | 51 | 51/51 (100.0%) | 0.314 | 14 | 2 |
| 3–4 | random | 60 | 59/60 (98.3%) | 3.870 | 14 | 4 |
| 3–4 | sat | 52 | 51/52 (98.1%) | 4.870 | 16 | 4 |
| 3–4 | unsat | 72 | 72/72 (100.0%) | 1.448 | 15.5 | 4 |
| 5–6 | random | 33 | 28/33 (84.8%) | 16.246 | 18 | 6 |
| 5–6 | sat | 26 | 16/26 (61.5%) | 19.951 | 19.5 | 6 |
| 5–6 | unsat | 32 | 32/32 (100.0%) | 4.025 | 18.5 | 5 |
| 7+ | random | 61 | 30/61 (49.2%) | 68.339 | 42 | 10 |
| 7+ | sat | 73 | 37/73 (50.7%) | 18.077 | 36 | 8 |
| 7+ | unsat | 31 | 26/31 (83.9%) | 18.244 | 20 | 8 |

## Pointwise uncertainty for mixed-grammar cells

Completion intervals are Wilson 95% intervals over independent inputs. Capped wall-cost intervals are input-bootstrap 95% intervals (2,000 resamples). Capped wall cost includes post-handshake communication/exit overhead and stops at the cutoff; it is not the internal solver time or the uncensored mean.

| budget | equations | family | completion %, 95% interval | mean capped wall ms, 95% interval |
|---|---|---|---|---|
| 3 | 1 | random | 100% [83.9, 100.0] | 1.2 [0.8, 1.6] |
| 3 | 1 | sat | 100% [83.9, 100.0] | 5.2 [2.1, 8.8] |
| 3 | 1 | unsat | 100% [83.9, 100.0] | 3.0 [1.4, 5.1] |
| 3 | 3 | random | 100% [83.9, 100.0] | 23.5 [6.5, 52.9] |
| 3 | 3 | sat | 85% [64.0, 94.8] | 124.6 [48.7, 211.8] |
| 3 | 3 | unsat | 100% [83.9, 100.0] | 2.0 [1.3, 2.7] |
| 5 | 1 | random | 100% [83.9, 100.0] | 3.8 [1.8, 7.1] |
| 5 | 1 | sat | 95% [76.4, 99.1] | 27.6 [1.3, 78.6] |
| 5 | 1 | unsat | 100% [83.9, 100.0] | 2.1 [1.1, 3.6] |
| 5 | 3 | random | 65% [43.3, 81.9] | 242.8 [155.3, 332.9] |
| 5 | 3 | sat | 75% [53.1, 88.8] | 158.1 [74.1, 252.2] |
| 5 | 3 | unsat | 100% [83.9, 100.0] | 13.2 [2.2, 33.9] |
| 7 | 1 | random | 95% [76.4, 99.1] | 44.7 [11.1, 98.9] |
| 7 | 1 | sat | 85% [64.0, 94.8] | 81.5 [8.5, 156.9] |
| 7 | 1 | unsat | 100% [83.9, 100.0] | 6.4 [1.9, 14.0] |
| 7 | 3 | random | 30% [14.5, 51.9] | 396.9 [315.5, 462.6] |
| 7 | 3 | sat | 30% [14.5, 51.9] | 382.7 [289.9, 463.5] |
| 7 | 3 | unsat | 90% [69.9, 97.2] | 58.5 [8.0, 132.3] |

## Unconditioned random answers

- h: 27 SAT, 85 UNSAT, 8 unknown at cutoff (n=120).
- E: 23 SAT, 81 UNSAT, 16 unknown at cutoff (n=120).
- mixed: 28 SAT, 70 UNSAT, 22 unknown at cutoff (n=120).

## Longer-cutoff mixed-grammar follow-up

A fixed subset (the first sample indices, not selected by observed difficulty) was rerun at 3 seconds. These inputs overlap the primary run and are not additional independent samples.

Of 90 rerun inputs, 6 primary timeouts completed, 6 remained censored, and 0 formerly completed inputs timed out.

| budget | family | n | completed | median ms, completed only | median nodes | median E count |
|---|---|---|---|---|---|---|
| 3 | random | 10 | 10/10 (100.0%) | 1.483 | 12 | 2 |
| 3 | sat | 10 | 10/10 (100.0%) | 1.252 | 13 | 2 |
| 3 | unsat | 10 | 10/10 (100.0%) | 0.182 | 10.5 | 0.5 |
| 5 | random | 10 | 9/10 (90.0%) | 6.341 | 20 | 2.5 |
| 5 | sat | 10 | 9/10 (90.0%) | 3.541 | 22.5 | 4.5 |
| 5 | unsat | 10 | 10/10 (100.0%) | 0.902 | 16.5 | 3 |
| 7 | random | 10 | 9/10 (90.0%) | 41.742 | 28 | 4.5 |
| 7 | sat | 10 | 7/10 (70.0%) | 9.698 | 32 | 5 |
| 7 | unsat | 10 | 10/10 (100.0%) | 2.702 | 21 | 3.5 |

## Decision versus extracted witness

60 planted-SAT inputs, with three fresh-process repetitions per mode.

All repetitions completed: decision 53/60; extracted witness 53/60. 0 inputs completed in every decision run but timed out in at least one witness run.

For the 53 fully observed input pairs, the median ratio of per-input median witness/decision times was 1.09× (input-bootstrap 95% interval 1.04–1.16×). This ratio is conditional on completion in both modes; it does not summarize censored inputs.

Completed witnesses are small in this cohort: 18 have zero total graph weight; median weight 1, maximum 4. Weight counts canonical summands, E edges and word lengths across queried variables. This cohort does not exercise worst-case large-output expansion.

## Reproducibility and uncertainty

Each run directory contains `cases.jsonl`, `runs.jsonl`, `metadata.json`, and `summary.json`. The last file gives every sampling cell separately, with Wilson completion intervals and input-clustered bootstrap intervals for mean capped wall cost. These are pointwise 95% intervals, not simultaneous claims across all cells. Repetitions are not counted as independent inputs.

The capped cost estimates E[min(T, cutoff)], not uncensored mean runtime. Unrestricted mean runtime and high percentiles beyond the censoring threshold are not identifiable from this experiment. No asymptotic exponent was fitted to these small, differently shaped inputs.

Compilation, generation, parsing and startup are excluded from internal solver times. Fresh processes run serially in shuffled order. Memory is not measured because the macOS RSS collection command is blocked by the sandbox. Frequency, thermal state and unrelated host activity are uncontrolled. Pilot observations are excluded from the primary statistics.

Primary executable SHA-256: `c111f88da2c62e2e738450bf222091900a99fda9099fc084d3f9f4c6a94bc9d9`.

Primary source SHA-256: `fb94459acc34bc117f7924dcc62d1a38d2a132db67f1a7140b1bd46dcd8a579a`.
