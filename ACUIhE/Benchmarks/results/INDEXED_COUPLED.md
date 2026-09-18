# Coupled-system comparison after indexed propagation

These are the same twelve connected systems as the retained
[baseline](coupled-baseline/REPORT.md): six deterministic families, each at
100 and 200 equations. They are not independent equations batched together.
Every SAT family has the known solution mapping every variable to a; the
UNSAT chain would equate distinct free constants a and b.

Three serial, shuffled fresh-process decision runs per input, five-second
post-parse wall deadline. Solver preprocessing is included. Times below are
internal medians over the three completed runs; timeouts are not UNSAT.
Repetitions are not independent workload samples. No compilation or other
solver benchmark ran concurrently.

| Family | Equations | Previous | Current |
|---|---:|---:|---:|
| SAT chain | 100 | 0/3 within 5 s | 3/3; 0.098 s |
| SAT chain | 200 | 0/3 within 5 s | 3/3; 0.386 s |
| UNSAT chain | 100 | 0/3 within 5 s | 3/3; 0.055 s |
| UNSAT chain | 200 | 0/3 within 5 s | 3/3; 0.217 s |
| Homomorphism cycle | 100 | 3/3; 3.428 s | 3/3; 1.352 s |
| Homomorphism cycle | 200 | 0/3 within 5 s | 0/3 within 5 s |
| Union cycle | 100 and 200 | 0/3 each within 5 s | 0/3 each within 5 s |
| E cycle | 100 and 200 | 0/3 each within 5 s | 0/3 each within 5 s |
| Mixed cycle | 100 and 200 | 0/3 each within 5 s | 0/3 each within 5 s |

All completed answers agree with the mathematical labels. The baseline also
has selected 30-second follow-ups: its SAT chain at 100 timed out there.
Those follow-ups are not pooled with the five-second comparison.

The changes clearly help the chains and the smaller homomorphism cycle. They
do not establish practical performance for arbitrary large coupled systems.
In particular, the union and E-heavy cycles remain unresolved at this deadline.
No complexity theorem follows from these sizes. The runs are historical, not
interleaved; machine load and thermal state remain uncontrolled.

## Records and reproduction

- [Baseline cases](coupled-baseline/cases.json), [runs](coupled-baseline/runs.jsonl),
  [metadata](coupled-baseline/metadata.json).
- [Current cases](indexed-coupled/cases.json), [runs](indexed-coupled/runs.jsonl),
  [metadata](indexed-coupled/metadata.json), [summary](indexed-coupled/summary.json).
- [Replay driver](../coupled_replay.py); pass an unused output directory.
- Intermediate implementations are retained under `propagation-coupled`
  (three repeats) and `propagation-shared-coupled` (one exploratory repeat).
  They are not pooled with the current executable's observations.

Previous SHA-256: `37e246c2aadff2983c11819ce1da9ae1c29d7b9d560f85e6252ba2f0096e3c20`.

Current SHA-256: `3b6242ede5be37dc0a9f67fab803e1d0121b8b808c176d40da4195d35a5580d8`.
