# Longer-cutoff follow-up of the shared E-rule solver

The primary experiment completed 966/1080 inputs at a 0.5-second deadline. All 114 timeouts were replayed, without changing their inputs, at 10 seconds per input. The compiled executable is identical.

The follow-up completed **63/114** previously timed-out inputs. This brings cumulative completion to **1029/1080 (95.3%)**. **51** inputs remain censored at 10 seconds. Worker errors and known-answer disagreements: zero (33 independently labelled follow-up completions).

## Interpretation

This is a conditional follow-up of the slow tail, not a new random sample. The earlier completed inputs were not rerun. Cumulative totals combine their recorded answers with the follow-up; they are not a fresh whole-cohort measurement at the new deadline. A timeout remains unknown and is never counted as an UNSAT answer. These are decision measurements, not witness-extraction measurements.

Startup and parsing are outside the timed region. Fresh processes run serially in shuffled order, with the same timing protocol as the primary experiment. The deadline covers post-handshake wall time; internal solver time excludes communication and exit overhead. Host load and thermal state are uncontrolled. Results do not extrapolate to longer cutoffs, larger inputs, or arbitrary workloads.

## Completion by grammar

| profile | primary completed | newly completed | cumulative completed | still timed out |
|---|---|---|---|---|
| h | 338/360 | 15 | 353/360 | 7 |
| E | 318/360 | 22 | 340/360 | 20 |
| mixed | 310/360 | 26 | 336/360 | 24 |

## Observed cumulative completion versus budget

Intermediate budgets are read from the follow-up's successful wall times; they were not separate reruns. Earlier primary completions are carried forward. At the actual deadlines, completion uses the supervisor's recorded status.

| per-input budget, seconds | cumulative completed | percentage |
|---|---|---|
| 0.5 | 966/1080 | 89.4% |
| 1 | 991/1080 | 91.8% |
| 3 | 1017/1080 | 94.2% |
| 5 | 1024/1080 | 94.8% |
| 10 | 1029/1080 | 95.3% |

Among the 63 follow-up completions only, internal solver time ranged from 0.493 to 7.894 seconds, with median 1.335 seconds. This conditional median omits all remaining timeouts.

## Follow-up answers and remaining cases

| input family | newly completed SAT | newly completed UNSAT | remaining timeouts |
|---|---|---|---|
| sat | 26 | 0 | 35 |
| unsat | 0 | 7 | 0 |
| random | 0 | 30 | 16 |

Remaining input IDs (complete equations and their metadata are retained in `cases.jsonl`):

- `20260910/E/5/1/sat/1`
- `20260910/E/5/1/sat/2`
- `20260910/E/5/3/sat/13`
- `20260910/E/5/3/sat/2`
- `20260910/E/7/3/random/11`
- `20260910/E/7/3/random/13`
- `20260910/E/7/3/random/16`
- `20260910/E/7/3/random/17`
- `20260910/E/7/3/random/19`
- `20260910/E/7/3/random/4`
- `20260910/E/7/3/sat/0`
- `20260910/E/7/3/sat/1`
- `20260910/E/7/3/sat/10`
- `20260910/E/7/3/sat/11`
- `20260910/E/7/3/sat/17`
- `20260910/E/7/3/sat/18`
- `20260910/E/7/3/sat/19`
- `20260910/E/7/3/sat/2`
- `20260910/E/7/3/sat/4`
- `20260910/E/7/3/sat/5`
- `20260910/h/5/3/sat/12`
- `20260910/h/5/3/sat/16`
- `20260910/h/5/3/sat/17`
- `20260910/h/7/3/random/16`
- `20260910/h/7/3/sat/0`
- `20260910/h/7/3/sat/11`
- `20260910/h/7/3/sat/18`
- `20260910/mixed/3/3/sat/18`
- `20260910/mixed/5/3/random/10`
- `20260910/mixed/5/3/random/4`
- `20260910/mixed/5/3/sat/11`
- `20260910/mixed/5/3/sat/14`
- `20260910/mixed/5/3/sat/19`
- `20260910/mixed/5/3/sat/2`
- `20260910/mixed/7/1/random/16`
- `20260910/mixed/7/1/sat/14`
- `20260910/mixed/7/3/random/10`
- `20260910/mixed/7/3/random/14`
- `20260910/mixed/7/3/random/15`
- `20260910/mixed/7/3/random/18`
- `20260910/mixed/7/3/random/2`
- `20260910/mixed/7/3/random/7`
- `20260910/mixed/7/3/sat/0`
- `20260910/mixed/7/3/sat/1`
- `20260910/mixed/7/3/sat/11`
- `20260910/mixed/7/3/sat/16`
- `20260910/mixed/7/3/sat/17`
- `20260910/mixed/7/3/sat/19`
- `20260910/mixed/7/3/sat/4`
- `20260910/mixed/7/3/sat/5`
- `20260910/mixed/7/3/sat/9`

## Provenance

Primary run: 2026-09-10T02:07:30.485855+00:00; follow-up: 2026-09-10T02:16:31.994843+00:00.

Raw data: [primary](shared-rules-decision), [follow-up](shared-rules-timeouts-10s). See [benchmark methodology](../README.md) for reproduction commands.

Executable SHA-256 (both stages): `c111f88da2c62e2e738450bf222091900a99fda9099fc084d3f9f4c6a94bc9d9`.
