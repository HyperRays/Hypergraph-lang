# Shared E-rule solver: historical benchmark comparison

Every run uses the full ACUIhE solver. The current implementation replays the exact retained inputs with the same cutoff, modes, repetitions and shuffled job order. This analysis checks complete case records and the full observation grid before pairing. Completed answers agree between implementations and with every available independent label; the analysis rejects errors or disagreements. Timeouts remain unknown, not UNSAT answers.

## How to read the comparisons

An input is completed only when all its repetitions complete. Newly completed/timed-out counts compare this criterion. Capped wall cost is min(post-handshake wall time, cutoff), averaged over repetitions and then inputs. It includes communication/exit overhead. A timeout contributes the cutoff to this statistic only, not an observed runtime.

Differences use 2,000 paired-input bootstrap resamples within the original profile/budget/equation-count/family cells. Intervals are pointwise 95% percentile intervals, not simultaneous guarantees. Input repetitions are not independent samples. Internal-time ratios first take each input's median per implementation, then their ratio (previous/current; larger than one favors current). They are conditional on completion in both implementations and do not measure the censored tail. Their intervals resample only this commonly completed subset, within its observed cells.

The cohorts overlap: the paired and extended inputs are subsets of the primary cohort. Do not add their input counts. These are historical measurements, not contemporaneously interleaved executions. Machine load, clock frequency and thermal state are uncontrolled; bootstrap intervals do not account for that systematic uncertainty. These results do not establish asymptotic complexity or real-world workload performance. See [methodology](../README.md) and [current detailed results](SHARED_RULES_REPORT.md).

## Primary decision

1080 inputs; cutoff 0.5 s; 1 repetition(s) per mode.

Previous: 2026-09-10T00:34:04.104589+00:00; current: 2026-09-10T02:07:30.485855+00:00.

Raw data: [previous](decision), [current](shared-rules-decision).

### decision

| profile | inputs | previous completed | current completed | newly completed | newly timed out | incomplete in both |
|---|---|---|---|---|---|---|
| all | 1080 | 641/1080 (59.4%) | 966/1080 (89.4%) | 325 | 0 | 114 |
| E | 360 | 129/360 (35.8%) | 318/360 (88.3%) | 189 | 0 | 42 |
| h | 360 | 321/360 (89.2%) | 338/360 (93.9%) | 17 | 0 | 22 |
| mixed | 360 | 191/360 (53.1%) | 310/360 (86.1%) | 119 | 0 | 50 |

| profile | previous mean capped wall ms | current mean capped wall ms | current − previous ms, paired 95% interval |
|---|---|---|---|
| all | 218.13 | 66.56 | -151.58 [-161.66, -141.79] |
| E | 335.18 | 73.38 | -261.80 [-281.71, -242.25] |
| h | 66.06 | 38.64 | -27.42 [-36.88, -18.79] |
| mixed | 253.16 | 87.65 | -165.51 [-186.41, -145.77] |

| profile | inputs completed in both | median per-input previous/current internal time ratio, 95% interval |
|---|---|---|
| all | 641 | 2.08× [1.89, 2.26] |
| E | 129 | 2.74× [1.98, 3.86] |
| h | 321 | 1.59× [1.39, 1.77] |
| mixed | 191 | 4.18× [2.89, 6.09] |

Previous executable SHA-256: `65f7d72461641021296cee7011cbf2daa4717f4b463c38dea20b1b536f09a309`.

Current executable SHA-256: `c111f88da2c62e2e738450bf222091900a99fda9099fc084d3f9f4c6a94bc9d9`.

## Witness extraction

60 inputs; cutoff 0.5 s; 3 repetition(s) per mode.

Previous: 2026-09-10T00:38:38.294442+00:00; current: 2026-09-10T02:09:25.418359+00:00.

Raw data: [previous](paired), [current](shared-rules-paired).

### decision

| profile | inputs | previous completed | current completed | newly completed | newly timed out | incomplete in both |
|---|---|---|---|---|---|---|
| all | 60 | 39/60 (65.0%) | 53/60 (88.3%) | 14 | 0 | 7 |
| E | 20 | 8/20 (40.0%) | 16/20 (80.0%) | 8 | 0 | 4 |
| h | 20 | 18/20 (90.0%) | 20/20 (100.0%) | 2 | 0 | 0 |
| mixed | 20 | 13/20 (65.0%) | 17/20 (85.0%) | 4 | 0 | 3 |

| profile | previous mean capped wall ms | current mean capped wall ms | current − previous ms, paired 95% interval |
|---|---|---|---|
| all | 183.60 | 76.71 | -106.89 [-147.17, -68.01] |
| E | 300.74 | 118.98 | -181.76 [-278.73, -94.79] |
| h | 67.06 | 29.19 | -37.87 [-71.08, -7.67] |
| mixed | 183.00 | 81.96 | -101.04 [-174.67, -29.63] |

| profile | inputs completed in both | median per-input previous/current internal time ratio, 95% interval |
|---|---|---|
| all | 39 | 1.59× [1.14, 1.96] |
| E | 8 | 1.56× [1.15, 4.22] |
| h | 18 | 1.16× [1.09, 1.96] |
| mixed | 13 | 2.06× [1.13, 5.55] |

### witness

| profile | inputs | previous completed | current completed | newly completed | newly timed out | incomplete in both |
|---|---|---|---|---|---|---|
| all | 60 | 39/60 (65.0%) | 53/60 (88.3%) | 14 | 0 | 7 |
| E | 20 | 8/20 (40.0%) | 16/20 (80.0%) | 8 | 0 | 4 |
| h | 20 | 18/20 (90.0%) | 20/20 (100.0%) | 2 | 0 | 0 |
| mixed | 20 | 13/20 (65.0%) | 17/20 (85.0%) | 4 | 0 | 3 |

| profile | previous mean capped wall ms | current mean capped wall ms | current − previous ms, paired 95% interval |
|---|---|---|---|
| all | 185.22 | 76.98 | -108.24 [-148.38, -69.94] |
| E | 302.36 | 119.17 | -183.19 [-280.19, -93.92] |
| h | 67.52 | 29.75 | -37.77 [-71.74, -8.56] |
| mixed | 185.77 | 82.02 | -103.76 [-176.00, -31.75] |

| profile | inputs completed in both | median per-input previous/current internal time ratio, 95% interval |
|---|---|---|
| all | 39 | 1.56× [1.21, 1.96] |
| E | 8 | 1.56× [1.21, 6.59] |
| h | 18 | 1.30× [1.13, 1.84] |
| mixed | 13 | 1.99× [1.15, 6.48] |

Previous executable SHA-256: `65f7d72461641021296cee7011cbf2daa4717f4b463c38dea20b1b536f09a309`.

Current executable SHA-256: `c111f88da2c62e2e738450bf222091900a99fda9099fc084d3f9f4c6a94bc9d9`.

## Longer-cutoff mixed inputs

90 inputs; cutoff 3 s; 1 repetition(s) per mode.

Previous: 2026-09-10T00:40:21.322688+00:00; current: 2026-09-10T02:10:07.596080+00:00.

Raw data: [previous](extended), [current](shared-rules-extended).

### decision

| profile | inputs | previous completed | current completed | newly completed | newly timed out | incomplete in both |
|---|---|---|---|---|---|---|
| mixed | 90 | 54/90 (60.0%) | 84/90 (93.3%) | 30 | 0 | 6 |

| profile | previous mean capped wall ms | current mean capped wall ms | current − previous ms, paired 95% interval |
|---|---|---|---|
| mixed | 1317.92 | 276.66 | -1041.26 [-1240.23, -833.18] |

| profile | inputs completed in both | median per-input previous/current internal time ratio, 95% interval |
|---|---|---|
| mixed | 54 | 6.36× [2.65, 13.90] |

Previous executable SHA-256: `65f7d72461641021296cee7011cbf2daa4717f4b463c38dea20b1b536f09a309`.

Current executable SHA-256: `c111f88da2c62e2e738450bf222091900a99fda9099fc084d3f9f4c6a94bc9d9`.
