# ACUIhE paired fuzz benchmark

This benchmark compares the original, reachable-state optimized,
witness-carrying shortcut, and proved FILO solvers on identical,
deterministically generated inequalities. It is separate from the solver
implementation.

## Generated grammar

The current test alphabet contains two constants, one variable, and one
homomorphism. At positive requested depth, a raw term node is selected using:

- 10% leaf (`0`, a constant, or the variable);
- 45% addition;
- 20% homomorphism;
- 25% `E`.

Children receive the preceding maximum depth. Both sides are normalized before
timing. The worker records the realized node count, constructor counts, and
syntax depth in the CSV.

The driver samples three explicitly separate distributions:

- `random`: two independently generated grammar terms;
- `sat`: `left ≤ left + slack`, providing a guaranteed satisfiable control;
- `cyclic`: `E(X + a + payload) + b ≤ X`, providing cyclic-UNSAT stress cases
  in the samples completed by both solvers.

Each solver runs in a fresh process. Solver order rotates between cases,
only the solver call is included in `elapsed_ms`, and an external timeout kills
individual hard cases. A matching seed always denotes the same inequality.

The shortcut and FILO workers ignore `--shallow-bound`. The shortcut solver's
shallow prepass height is an internal performance constant; FILO has no
user-supplied search bound and uses only proved finite cardinality bounds.

## Reproduction

```console
lake build acuihe-fuzz
uv run python Benchmarks/run_fuzz.py \
  --samples 25 --depths 1 --families random,sat,cyclic \
  --timeout 5 --shallow-bound 8

uv run python Benchmarks/run_fuzz.py \
  --samples 25 --depths 2 --families random,sat \
  --timeout 5 --shallow-bound 8
```

The seed defaults to `20260903`. Use `--seed`, `--samples`, `--depths`, and
`--families` to define a different reproducible workload distribution.

## September 2026 sample

The checked-in CSV files contain 125 generated cases using seed `20260903`,
one repetition, a five-second per-solver timeout, and the optimized solver's
default shallow bound of eight.

| Distribution | Depth | Cases completed by both | Original median | Optimized median | Geometric-mean speedup | Original timeouts | Optimized timeouts |
|---|---:|---:|---:|---:|---:|---:|---:|
| Random | 1 | 24/25 | 6.5 ms | 2 ms | 1.48x | 1 | 1 |
| SAT extension | 1 | 24/25 | 10.5 ms | 3 ms | 2.81x | 1 | 0 |
| Cyclic | 1 | 21/25 | 1074 ms | 1205 ms | 0.88x | 4 | 3 |
| Random | 2 | 17/25 | 26 ms | 11 ms | 1.55x | 8 | 3 |
| SAT extension | 2 | 14/25 | 52 ms | 23.5 ms | 3.15x | 11 | 3 |

Across the 100 cases completed by both solvers, the geometric-mean speedup was
1.73x and the median fell from 29 ms to 13 ms. The optimized solver won 54,
lost 31, and tied 15 paired cases. It timed out 10 times versus 25 for the
original, including 15 cases where only the optimized solver completed. There
were no cases with the reverse timeout and no classification disagreements.
Because the two requested-depth strata reuse the same seed sequence, this
combined summary is descriptive rather than an independent-sample hypothesis
test.

The result is workload-dependent:

- On the 70 completed SAT cases, the geometric-mean speedup was 2.37x; the
  optimized solver won 54, lost 1, and tied 15.
- On the 30 completed UNSAT cases, it was 0.83x; every optimized run was
  slower. These completed-pair statistics omit timed-out cases.
- Accordingly, the combined completed-pair p90 and p95 were worse for the
  optimized solver, even though its total timeout rate was substantially
  lower. The repeated shallow phase is the likely source of this UNSAT cost.

A matched depth-one run with `shallowBound = 0` reduced the cyclic regression
but removed most of the SAT improvement: its overall geometric-mean speedup
was 1.04x rather than 1.58x for the default-eight run. This suggests an
adaptive or shared-work shallow strategy rather than globally setting the
bound to zero.

## Shortcut-backend validation

`fuzz_shortcut_depth1_seed20260903_n10.csv` is a 30-case, three-way matched
smoke distribution (10 cases per family, five-second timeout). There were no
classification disagreements among completed optimized/shortcut pairs. Each
backend timed out on the same hard cyclic case. Among the other 29 pairs, the
optimized and shortcut medians were both 16 ms; the shortcut geometric-mean
speedup was 0.99x (9 wins, 12 losses, and 8 ties). This shallow-heavy sample
therefore validates parity but does not demonstrate a general speedup: most
SAT instances finish in the common shallow prepass, while UNSAT instances
finish in the common productivity test. The shortcut-specific payoff is in
successful exact fallback beyond the prepass, which needs a dedicated hard-SAT
distribution for useful statistical measurement.

## FILO-backend measurement

The FILO worker was measured on 4 September 2026 with seed `20260903`, one
repetition, a five-second per-solver timeout, and shallow bound eight for the
optimized solver. Every invocation ran in a fresh process. Times below are the
solver-internal times for cases completed with matching classifications;
`FILO speedup` is optimized time divided by FILO time, so values below one
mean FILO was slower.

| Workload | Cases | Paired | Optimized median / p90 / p95 | FILO median / p90 / p95 | FILO geometric-mean speedup | Optimized timeouts | FILO timeouts |
|---|---:|---:|---:|---:|---:|---:|---:|
| Depth 1: random, SAT, cyclic (10 each) | 30 | 29 | 9.77 / 139.75 / 166.16 ms | 11.81 / 22.34 / 34.28 ms | 1.18x | 1 | 0 |
| Depth 2: random, SAT (10 each) | 20 | 20 | 13.61 / 182.68 / 405.12 ms | 23.36 / 162.95 / 486.23 ms | 0.66x | 0 | 0 |

There were no classification disagreements on any jointly completed case.
At depth one, FILO was slower on easy random and guaranteed-SAT inputs but
substantially faster on cyclic inputs: its cyclic median was 16.76 ms versus
138.91 ms and it won all nine jointly completed cyclic cases, for an 8.28x
geometric-mean speedup. FILO also completed the remaining cyclic case in
217 ms while optimized timed out.

At depth two, FILO completed all cases but lost 14 of the 20 paired timings,
principally on the guaranteed-SAT family. On random inputs its
geometric-mean speedup was 1.18x. The former FILO timeout—a random seven-node
input containing two `E` operators—now completes in 601 ms versus 4086 ms for
optimized. The proved FILO kernel is consequently competitive on the harder
and cyclic inputs, although its easy-SAT overhead remains a clear target.

The worker additionally profiles FILO at the `solveColumnFamilyCached?`
boundary. Each complete lookup/solve call, including construction of the
matrix-column systems supplied to it, is charged to ACUIh. Configuration-list
enumeration, validity filtering, witness reconstruction, the final ground
check, loop bookkeeping, and the small timing overhead are charged to `E`.

| Workload | Completed FILO cases | Direct `E` time | ACUIh-call time | Configurations / valid configurations |
|---|---:|---:|---:|---:|
| Depth 1 | 30 | 17.24 ms (2.7%) | 617.05 ms (97.3%) | 140 / 98 |
| Depth 2 | 20 | 27.79 ms (1.7%) | 1612.33 ms (98.3%) | 113 / 59 |

Thus direct outer-`E` computation is not the current runtime bottleneck.
However, `E` controls the number of ACUIh calls: the 98 and 59 valid
configurations above each trigger a column-family lookup/solve. The new
extensional system cache shares identical ACUIh results between those
configurations; a future `E` algorithm can still improve matters by avoiding
configurations altogether.

The raw results are in
`results/fuzz_filo_depth1_seed20260903_n10.csv` and
`results/fuzz_filo_depth2_seed20260903_n10.csv`.

## Plots and significance

Generate Matplotlib PNG and SVG plots, plus a machine-readable statistical
summary, with:

```console
uv run --with matplotlib python Benchmarks/plot_fuzz.py
```

The significance figure reports geometric-mean paired speedups on the log
runtime scale, percentile-bootstrap 95% intervals, two-sided paired sign-flip
randomization tests, and Holm-adjusted p-values across the eight displayed
comparisons. Exact sign-test p-values and win/loss/tie counts are also written
to `Benchmarks/results/fuzz_statistical_summary.csv`. Completed pairs with
different classifications or a timeout are excluded from effect estimation;
timeouts remain visible in the runtime and paired scatter plots.
