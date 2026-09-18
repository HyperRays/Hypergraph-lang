# Canonical preprocessing: historical benchmark comparison

Every run uses the full ACUIhE solver. The current implementation replays the exact retained inputs with the same cutoff, modes, repetitions and shuffled job order. This analysis checks complete case records and the full observation grid before pairing. Completed answers agree between implementations and with every available independent label; the analysis rejects errors or disagreements. Timeouts remain unknown, not UNSAT answers.

The change normalizes full terms before preparation, removes canonical identities
and duplicate equation pairs, and names E children by canonical graph equality.
The underlying shared E search and FILO procedures are unchanged. Preprocessing
is inside the timed solver operation, not performed by the benchmark harness.

At 0.5 seconds, 991/1,080 inputs complete, versus 966 previously: 14 additional
E-profile inputs and 11 mixed-profile inputs, with no previously completed input
timing out. The 89 remaining timeouts are unresolved within this budget. This is
not a uniform speedup: among commonly completed primary inputs, the median
previous/current internal-time ratio is 0.97, indicating some overhead. Mean
capped wall cost nevertheless falls from 66.56 ms to 58.17 ms. In the smaller
paired cohort, completion improves from 53/60 to 54/60 in both modes, requiring
all three repetitions to finish.

## How to read the comparisons

An input is completed only when all its repetitions complete. Newly completed/timed-out counts compare this criterion. Capped wall cost is min(post-handshake wall time, cutoff), averaged over repetitions and then inputs. It includes communication/exit overhead. A timeout contributes the cutoff to this statistic only, not an observed runtime.

Differences use 2,000 paired-input bootstrap resamples within the original profile/budget/equation-count/family cells. Intervals are pointwise 95% percentile intervals, not simultaneous guarantees. Input repetitions are not independent samples. Internal-time ratios first take each input's median per implementation, then their ratio (previous/current; larger than one favors current). They are conditional on completion in both implementations and do not measure the censored tail. Their intervals resample only this commonly completed subset, within its observed cells.

The cohorts overlap: the paired inputs are a subset of the primary cohort. Do not add their input counts. These are historical measurements, not contemporaneously interleaved executions. Machine load, clock frequency and thermal state are uncontrolled; bootstrap intervals do not account for that systematic uncertainty. These results do not establish asymptotic complexity or real-world workload performance. See [methodology](../README.md) and [earlier shared-rule results](SHARED_RULES_REPORT.md). The earlier 10-second follow-up used the previous executable and is not combined with these results.

## Primary decision

1080 inputs; cutoff 0.5 s; 1 repetition(s) per mode.

Previous: 2026-09-10T02:07:30.485855+00:00; current: 2026-09-10T12:18:21.922134+00:00.

Raw data: [previous](shared-rules-decision), [current](canonical-decision).

### decision

| profile | inputs | previous completed | current completed | newly completed | newly timed out | incomplete in both |
|---|---|---|---|---|---|---|
| all | 1080 | 966/1080 (89.4%) | 991/1080 (91.8%) | 25 | 0 | 89 |
| E | 360 | 318/360 (88.3%) | 332/360 (92.2%) | 14 | 0 | 28 |
| h | 360 | 338/360 (93.9%) | 338/360 (93.9%) | 0 | 0 | 22 |
| mixed | 360 | 310/360 (86.1%) | 321/360 (89.2%) | 11 | 0 | 39 |

| profile | previous mean capped wall ms | current mean capped wall ms | current − previous ms, paired 95% interval |
|---|---|---|---|
| all | 66.56 | 58.17 | -8.39 [-11.49, -5.08] |
| E | 73.38 | 60.73 | -12.65 [-20.88, -5.27] |
| h | 38.64 | 38.33 | -0.31 [-0.79, 0.03] |
| mixed | 87.65 | 75.45 | -12.19 [-18.10, -6.20] |

| profile | inputs completed in both | median per-input previous/current internal time ratio, 95% interval |
|---|---|---|
| all | 966 | 0.97× [0.96, 0.99] |
| E | 318 | 0.89× [0.86, 0.93] |
| h | 338 | 0.99× [0.99, 1.00] |
| mixed | 310 | 0.95× [0.92, 0.98] |

Previous executable SHA-256: `c111f88da2c62e2e738450bf222091900a99fda9099fc084d3f9f4c6a94bc9d9`.

Current executable SHA-256: `37e246c2aadff2983c11819ce1da9ae1c29d7b9d560f85e6252ba2f0096e3c20`.

## Witness extraction

60 inputs; cutoff 0.5 s; 3 repetition(s) per mode.

Previous: 2026-09-10T02:09:25.418359+00:00; current: 2026-09-10T12:20:22.074103+00:00.

Raw data: [previous](shared-rules-paired), [current](canonical-paired).

### decision

| profile | inputs | previous completed | current completed | newly completed | newly timed out | incomplete in both |
|---|---|---|---|---|---|---|
| all | 60 | 53/60 (88.3%) | 54/60 (90.0%) | 1 | 0 | 6 |
| E | 20 | 16/20 (80.0%) | 17/20 (85.0%) | 1 | 0 | 3 |
| h | 20 | 20/20 (100.0%) | 20/20 (100.0%) | 0 | 0 | 0 |
| mixed | 20 | 17/20 (85.0%) | 17/20 (85.0%) | 0 | 0 | 3 |

| profile | previous mean capped wall ms | current mean capped wall ms | current − previous ms, paired 95% interval |
|---|---|---|---|
| all | 76.71 | 72.66 | -4.05 [-20.84, 7.41] |
| E | 118.98 | 109.33 | -9.65 [-58.68, 25.27] |
| h | 29.19 | 26.11 | -3.07 [-9.75, 0.58] |
| mixed | 81.96 | 82.53 | 0.57 [-1.19, 2.36] |

| profile | inputs completed in both | median per-input previous/current internal time ratio, 95% interval |
|---|---|---|
| all | 53 | 0.97× [0.96, 0.99] |
| E | 16 | 0.91× [0.62, 0.98] |
| h | 20 | 0.97× [0.93, 0.99] |
| mixed | 17 | 1.10× [0.98, 1.86] |

### witness

| profile | inputs | previous completed | current completed | newly completed | newly timed out | incomplete in both |
|---|---|---|---|---|---|---|
| all | 60 | 53/60 (88.3%) | 54/60 (90.0%) | 1 | 0 | 6 |
| E | 20 | 16/20 (80.0%) | 17/20 (85.0%) | 1 | 0 | 3 |
| h | 20 | 20/20 (100.0%) | 20/20 (100.0%) | 0 | 0 | 0 |
| mixed | 20 | 17/20 (85.0%) | 17/20 (85.0%) | 0 | 0 | 3 |

| profile | previous mean capped wall ms | current mean capped wall ms | current − previous ms, paired 95% interval |
|---|---|---|---|
| all | 76.98 | 73.21 | -3.77 [-19.45, 7.88] |
| E | 119.17 | 109.48 | -9.69 [-58.69, 23.54] |
| h | 29.75 | 27.11 | -2.63 [-10.01, 2.27] |
| mixed | 82.02 | 83.03 | 1.02 [-1.11, 3.43] |

| profile | inputs completed in both | median per-input previous/current internal time ratio, 95% interval |
|---|---|---|
| all | 53 | 1.00× [0.96, 1.01] |
| E | 16 | 0.92× [0.61, 0.99] |
| h | 20 | 1.00× [0.97, 1.01] |
| mixed | 17 | 1.11× [0.98, 1.88] |

Previous executable SHA-256: `c111f88da2c62e2e738450bf222091900a99fda9099fc084d3f9f4c6a94bc9d9`.

Current executable SHA-256: `37e246c2aadff2983c11819ce1da9ae1c29d7b9d560f85e6252ba2f0096e3c20`.
