# Indexed propagation and shared preprocessing: historical comparison

Every run uses the full ACUIhE solver. The current implementation replays the exact retained inputs with the same cutoff, modes, repetitions and shuffled job order. This analysis checks complete case records and the full observation grid before pairing. Completed answers agree between implementations and with every available independent label; the analysis rejects errors or disagreements. Timeouts remain unknown, not UNSAT answers.

The changes are necessary-clause propagation after partial choices, integer
indexing of component names, early literal-contradiction detection, compact
coordinate-support restrictions, shared column flattening, and exact exposed-E
cancellation after canonicalization. All are inside the measured solver call.
The implicit/shortcut word solver and the shared E group-search algorithm are
unchanged. There is no fallback or runtime substitution-validation pass.

At 0.5 seconds, completion improves from 991 to 1,055 of 1,080 inputs: 64 newly
completed and none newly timed out. The paired cohort improves from 54/60 to
60/60 in both decision and witness modes, with all three repetitions finishing.
This is not a uniform speedup: commonly completed small h-profile cases show
some added overhead. The improvements chiefly reduce the expensive tail.
The [large coupled-system comparison](INDEXED_COUPLED.md) records the separate
100/200-equation probes, including the families that remain slow.

## How to read the comparisons

An input is completed only when all its repetitions complete. Newly completed/timed-out counts compare this criterion. Capped wall cost is min(post-handshake wall time, cutoff), averaged over repetitions and then inputs. It includes communication/exit overhead. A timeout contributes the cutoff to this statistic only, not an observed runtime.

Differences use 2,000 paired-input bootstrap resamples within the original profile/budget/equation-count/family cells. Intervals are pointwise 95% percentile intervals, not simultaneous guarantees. Input repetitions are not independent samples. Internal-time ratios first take each input's median per implementation, then their ratio (previous/current; larger than one favors current). They are conditional on completion in both implementations and do not measure the censored tail. Their intervals resample only this commonly completed subset, within its observed cells.

The cohorts overlap: the paired inputs are a subset of the primary cohort. Do not add their input counts. These are historical measurements, not contemporaneously interleaved executions. Machine load, clock frequency and thermal state are uncontrolled; bootstrap intervals do not account for that systematic uncertainty. These results do not establish asymptotic complexity or real-world workload performance. See [methodology](../README.md) and [previous canonical-preprocessing results](CANONICALIZATION_COMPARISON.md).

## Primary decision

1080 inputs; cutoff 0.5 s; 1 repetition(s) per mode.

Previous: 2026-09-10T12:18:21.922134+00:00; current: 2026-09-10T15:39:45.129158+00:00.

Raw data: [previous](canonical-decision), [current](indexed-decision).

### decision

| profile | inputs | previous completed | current completed | newly completed | newly timed out | incomplete in both |
|---|---|---|---|---|---|---|
| all | 1080 | 991/1080 (91.8%) | 1055/1080 (97.7%) | 64 | 0 | 25 |
| E | 360 | 332/360 (92.2%) | 352/360 (97.8%) | 20 | 0 | 8 |
| h | 360 | 338/360 (93.9%) | 353/360 (98.1%) | 15 | 0 | 7 |
| mixed | 360 | 321/360 (89.2%) | 350/360 (97.2%) | 29 | 0 | 10 |

| profile | previous mean capped wall ms | current mean capped wall ms | current − previous ms, paired 95% interval |
|---|---|---|---|
| all | 58.17 | 24.93 | -33.24 [-38.55, -27.81] |
| E | 60.73 | 25.98 | -34.75 [-44.49, -25.69] |
| h | 38.33 | 17.35 | -20.98 [-30.23, -13.09] |
| mixed | 75.45 | 31.46 | -44.00 [-54.49, -34.38] |

| profile | inputs completed in both | median per-input previous/current internal time ratio, 95% interval |
|---|---|---|
| all | 991 | 1.05× [1.00, 1.10] |
| E | 332 | 1.08× [1.02, 1.14] |
| h | 338 | 0.91× [0.86, 0.96] |
| mixed | 321 | 1.17× [1.04, 1.35] |

Previous executable SHA-256: `37e246c2aadff2983c11819ce1da9ae1c29d7b9d560f85e6252ba2f0096e3c20`.

Current executable SHA-256: `3b6242ede5be37dc0a9f67fab803e1d0121b8b808c176d40da4195d35a5580d8`.

## Witness extraction

60 inputs; cutoff 0.5 s; 3 repetition(s) per mode.

Previous: 2026-09-10T12:20:22.074103+00:00; current: 2026-09-10T15:40:53.478156+00:00.

Raw data: [previous](canonical-paired), [current](indexed-paired).

### decision

| profile | inputs | previous completed | current completed | newly completed | newly timed out | incomplete in both |
|---|---|---|---|---|---|---|
| all | 60 | 54/60 (90.0%) | 60/60 (100.0%) | 6 | 0 | 0 |
| E | 20 | 17/20 (85.0%) | 20/20 (100.0%) | 3 | 0 | 0 |
| h | 20 | 20/20 (100.0%) | 20/20 (100.0%) | 0 | 0 | 0 |
| mixed | 20 | 17/20 (85.0%) | 20/20 (100.0%) | 3 | 0 | 0 |

| profile | previous mean capped wall ms | current mean capped wall ms | current − previous ms, paired 95% interval |
|---|---|---|---|
| all | 72.66 | 5.72 | -66.93 [-101.05, -34.71] |
| E | 109.33 | 3.94 | -105.39 [-182.25, -35.00] |
| h | 26.11 | 6.54 | -19.57 [-50.73, -2.00] |
| mixed | 82.53 | 6.69 | -75.84 [-144.18, -9.89] |

| profile | inputs completed in both | median per-input previous/current internal time ratio, 95% interval |
|---|---|---|
| all | 54 | 0.80× [0.65, 1.01] |
| E | 17 | 0.78× [0.66, 12.64] |
| h | 20 | 0.68× [0.54, 0.92] |
| mixed | 17 | 1.37× [0.56, 2.08] |

### witness

| profile | inputs | previous completed | current completed | newly completed | newly timed out | incomplete in both |
|---|---|---|---|---|---|---|
| all | 60 | 54/60 (90.0%) | 60/60 (100.0%) | 6 | 0 | 0 |
| E | 20 | 17/20 (85.0%) | 20/20 (100.0%) | 3 | 0 | 0 |
| h | 20 | 20/20 (100.0%) | 20/20 (100.0%) | 0 | 0 | 0 |
| mixed | 20 | 17/20 (85.0%) | 20/20 (100.0%) | 3 | 0 | 0 |

| profile | previous mean capped wall ms | current mean capped wall ms | current − previous ms, paired 95% interval |
|---|---|---|---|
| all | 73.21 | 5.86 | -67.35 [-103.39, -35.29] |
| E | 109.48 | 4.05 | -105.43 [-182.11, -36.58] |
| h | 27.11 | 6.69 | -20.42 [-53.45, -1.98] |
| mixed | 83.03 | 6.84 | -76.20 [-145.63, -22.47] |

| profile | inputs completed in both | median per-input previous/current internal time ratio, 95% interval |
|---|---|---|
| all | 54 | 0.81× [0.69, 1.03] |
| E | 17 | 0.78× [0.69, 3.18] |
| h | 20 | 0.70× [0.55, 0.93] |
| mixed | 17 | 1.32× [0.58, 2.16] |

Previous executable SHA-256: `37e246c2aadff2983c11819ce1da9ae1c29d7b9d560f85e6252ba2f0096e3c20`.

Current executable SHA-256: `3b6242ede5be37dc0a9f67fab803e1d0121b8b808c176d40da4195d35a5580d8`.
