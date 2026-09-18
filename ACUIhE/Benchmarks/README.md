# Grammar-fuzz performance benchmark

This directory measures the **current full `ACUIhE.Solver`**, including when
the generated input uses only one fragment. It does not benchmark the
standalone FILO or ACUIE solver in place of the full solver. Nothing here is
imported by the algebra, its proofs, or its solver. The harness does not
change solver definitions or proofs.

Canonical preprocessing is measured in
[results/CANONICALIZATION_COMPARISON.md](results/CANONICALIZATION_COMPARISON.md).
At the same 0.5-second cutoff, primary completion increased from 966/1,080 to
991/1,080; no previously completed input timed out. Both decision and witness
measurements include preprocessing inside the timed solver call.

The earlier shared E-rule implementation is measured in
[results/SHARED_RULES_REPORT.md](results/SHARED_RULES_REPORT.md), with an
[exact-input historical comparison](results/SHARED_RULES_COMPARISON.md).
The earlier measurements in [results/REPORT.md](results/REPORT.md) are retained
unchanged. At the same 0.5-second cutoff, primary completion increased from
641/1,080 to 966/1,080, with no previously completed input timing out.
These historical runs were not contemporaneously interleaved; the comparison
does not control for changes in host load or thermal state.

## Reproduce

```sh
lake build acuihe_bench
python3 -B Benchmarks/fuzz.py --output Benchmarks/results/my-decision-run \
  --samples 20 --timeout 0.5
```

The output directory must not already exist. All generated cases, including
timeouts, are retained. Replay exactly the same inputs at a different limit:

```sh
python3 -B Benchmarks/fuzz.py --output Benchmarks/results/my-replay \
  --replay Benchmarks/results/my-decision-run/cases.jsonl --timeout 5
```

Measure actual extraction on a smaller paired cohort, with three independent
process runs per input and mode:

```sh
python3 -B Benchmarks/fuzz.py --output Benchmarks/results/my-paired-run \
  --families sat --sizes 3 5 --samples 5 --modes decision witness \
  --repeats 3 --timeout 0.5
```

The retained longer-cutoff follow-up uses the first five mixed-grammar samples
from each primary cell (chosen by index, not their measured performance):

```sh
python3 -B Benchmarks/fuzz.py --output Benchmarks/results/my-extended-run \
  --profiles mixed --samples 5 --timeout 3
python3 -B Benchmarks/report.py --decision Benchmarks/results/my-decision-run \
  --paired Benchmarks/results/my-paired-run \
  --extended Benchmarks/results/my-extended-run \
  --output Benchmarks/results/my-report.md
```

### Exact replay of the retained shared-rule experiment

The following commands use the original case records, not newly generated
approximations. Choose unused output directories for another replay.

```sh
python3 -B Benchmarks/fuzz.py --output Benchmarks/results/shared-rules-decision \
  --replay Benchmarks/results/decision/cases.jsonl --timeout 0.5
python3 -B Benchmarks/fuzz.py --output Benchmarks/results/shared-rules-paired \
  --replay Benchmarks/results/paired/cases.jsonl \
  --modes decision witness --repeats 3 --timeout 0.5
python3 -B Benchmarks/fuzz.py --output Benchmarks/results/shared-rules-extended \
  --replay Benchmarks/results/extended/cases.jsonl --timeout 3
python3 -B Benchmarks/report.py \
  --decision Benchmarks/results/shared-rules-decision \
  --paired Benchmarks/results/shared-rules-paired \
  --extended Benchmarks/results/shared-rules-extended \
  --output Benchmarks/results/SHARED_RULES_REPORT.md
python3 -B Benchmarks/compare.py \
  --cohort 'Primary decision' Benchmarks/results/decision Benchmarks/results/shared-rules-decision \
  --cohort 'Witness extraction' Benchmarks/results/paired Benchmarks/results/shared-rules-paired \
  --cohort 'Longer-cutoff mixed inputs' Benchmarks/results/extended Benchmarks/results/shared-rules-extended \
  --output Benchmarks/results/SHARED_RULES_COMPARISON.md
```

`compare.py` analyzes saved observations only. It verifies exact case records,
complete run grids, equal cutoffs and job ordering, and agreement of completed
answers. Paired cost differences use 2,000 bootstrap resamples of inputs within
the original sampling cells. Its timing ratios use only inputs completed by
both implementations. The overlapping cohorts are not additional independent
inputs. Report generation does not alter any retained measurements.

### Retrying the slow tail

The [10-second follow-up](results/SHARED_RULES_TIMEOUTS_10S.md) replays all
114 primary timeouts, using the same compiled executable and unchanged input
records. It resolves 63 more cases, bringing cumulative completion to
1,029/1,080 (95.3%); 51 still time out. Reproduce with unused output paths:

```sh
python3 -B Benchmarks/fuzz.py \
  --output Benchmarks/results/shared-rules-timeouts-10s \
  --retry-timeouts Benchmarks/results/shared-rules-decision --timeout 10
python3 -B Benchmarks/followup_report.py \
  --primary Benchmarks/results/shared-rules-decision \
  --followup Benchmarks/results/shared-rules-timeouts-10s \
  --output Benchmarks/results/SHARED_RULES_TIMEOUTS_10S.md
```

`--retry-timeouts` requires a complete prior single-run decision cohort, a
longer cutoff, and the same executable hash. It records the conditional
selection in metadata. Per-cell statistics in this follow-up describe only
the selected timeouts. The follow-up report checks the exact selection and
combines newly completed answers with the earlier completions; those totals
are cumulative observations, not a fresh rerun of the whole cohort. Its
intermediate budget counts use observed wall times, not additional solver runs.

### Canonical preprocessing replay

The canonical-preprocessing comparison retains the same primary and paired
cohorts and uses the same cutoffs, repetitions, and shuffled job order:

```sh
python3 -B Benchmarks/fuzz.py --output Benchmarks/results/canonical-decision \
  --replay Benchmarks/results/shared-rules-decision/cases.jsonl --timeout 0.5
python3 -B Benchmarks/fuzz.py --output Benchmarks/results/canonical-paired \
  --replay Benchmarks/results/shared-rules-paired/cases.jsonl \
  --modes decision witness --repeats 3 --timeout 0.5
python3 -B Benchmarks/compare.py \
  --cohort 'Primary decision' Benchmarks/results/shared-rules-decision Benchmarks/results/canonical-decision \
  --cohort 'Witness extraction' Benchmarks/results/shared-rules-paired Benchmarks/results/canonical-paired \
  --output Benchmarks/results/CANONICALIZATION_COMPARISON.md
```

Choose unused output paths when rerunning. The previous 10-second follow-up
belongs to the pre-canonicalization executable; it cannot be combined with
these new measurements as though they measured the same solver version.

### Indexed propagation and shared preprocessing replay

The current replay records all preprocessing, indexing, propagation, and
search inside the timed operation. Use unused output directories:

```sh
python3 -B Benchmarks/fuzz.py --output Benchmarks/results/indexed-decision \
  --replay Benchmarks/results/canonical-decision/cases.jsonl --timeout 0.5
python3 -B Benchmarks/fuzz.py --output Benchmarks/results/indexed-paired \
  --replay Benchmarks/results/canonical-paired/cases.jsonl \
  --modes decision witness --repeats 3 --timeout 0.5
python3 -B Benchmarks/coupled_replay.py \
  --cases Benchmarks/results/coupled-baseline/cases.json \
  --output Benchmarks/results/indexed-coupled --timeout 5 --repeats 3
```

The coupled cohort has six deterministic connected families at 100 and 200
equations. Its repetitions measure repeatability, not independently sampled
workloads. Earlier results and intermediate implementation measurements are
retained separately; results from different executable hashes are not pooled.

### Measured operations

`decision` calls `Solver.isUnifiable`. `witness` calls `Solver.solve`, queries
each declared variable, and traverses every resulting canonical graph using
`Graph.fold`. It includes extraction **and** that traversal. This forces the
result beyond a substitution closure. The emitted graph weight counts
summands, E edges, and homomorphism-word lengths; it is not a memory measure.

## Sampling distribution

The grammar is `0 | c | X | t + t | h_r(t) | E(t)`, with two ordinary
constants, two homomorphism labels, and normally two variables. Profiles `h`,
`E`, and `mixed` permit only h, only E, or both unary operators, respectively;
they do not require those operators to occur. The actual operator counts and
depths are recorded.

The size parameter is the **exact node budget of a generated seed term**,
not the final problem size. At budget one, leaves are uniform over zero,
the constants, and the available variables. At budget two, a unary operator
is necessary. At larger budgets, each allowed unary operator has weight one
and addition has weight two. Addition's left-child budget is uniform over
the possible positive splits. This is intentionally a stated recursive
distribution, **not** uniform sampling over syntax trees or algebraic classes.

Three separate populations are sampled:

- **Planted SAT:** generate one ground substitution shared by every equation
  of the system. Each variable value has one or two nodes (one-node values
  are more frequent). Generate symbolic seed terms, ensuring each has a
  variable, and equate them with their instantiated ground terms. Ground
  sides are perturbed using commutativity, addition of zero, and h
  distribution. No distribution law is used for E. An independent Python
  ground normalizer checks the planted substitution for every equation
  before measurement. The substitution is stored with the case.
- **Known UNSAT, single equation:** start from the same planted construction
  and add a fresh constant to the symbolic left side. The ground right side
  contains neither variables nor that constant. The fresh root summand
  survives every substitution and cannot occur on the right in canonical
  form, so the equation has no unifier.
- **Known UNSAT, systems:** the first equations fix all variables to
  generated ground values. The last equates a random symbolic term with its
  ground instance plus a fresh constant. Under the anchors, these sides
  have different canonical forms. Every possible unifier must satisfy the
  anchors, so no simultaneous unifier exists. These are global
  inconsistencies, not a separately appended `c = d` contradiction.
- **Unconditioned random:** generate both sides independently, without
  a satisfiability filter. Completed answers can be classified using the
  verified solver. A timed-out input remains of unknown classification.

The UNSAT justification is mathematical and independent of the solver; it
is not a newly formalized generator theorem. The Python normalizer is an
experimental cross-check, not part of the trusted Lean proof. Positive and
negative populations are deliberately synthetic and their hardness cannot
be assumed representative of application workloads. In particular, the
fresh-constant single-equation family is structurally easy. Duplicate input
samples are retained (sampling with replacement) and unique counts reported.

## Timing and statistics

Each measurement uses a fresh compiled process. JSON parsing and process
startup happen before the `ready` handshake. The supervisor then sends `go`.
Lean records monotonic nanoseconds around the solver operation; output
serialization is outside that internal interval. A separate wall deadline
covers the interval from sending `go` through process exit. Three untimed
warmup processes precede the experiment. Runs are serial and their order is
shuffled reproducibly. **Do not run two benchmark drivers concurrently.**

- `cases.jsonl`: complete inputs, independent labels/certificates, per-case
  deterministic seeds, grammar parameters, and actual structural metrics.
- `runs.jsonl`: flushed after each run; successful answers/internal times,
  wall times, timeouts, and errors are distinguished. Any label disagreement
  or worker error stops the run and preserves the diagnostic.
- `metadata.json`: command parameters, platform, toolchain, executable hash,
  source fingerprint, and measurement limitations.
- `summary.json`: per-cell completion rates with Wilson 95% intervals;
  conditional completed-run medians/p90s; and mean **capped wall cost** with
  2,000-resample percentile bootstrap intervals, clustered by input when
  there are repetitions. Each input, not each repeated run, is a statistical
  sample. The intervals are pointwise, not simultaneous over all cells.

Timeouts are right-censored. Completed-only medians are explicitly conditional
and must not be presented as unconditional performance. Capped wall cost
estimates `E[min(T, cutoff)]`, not mean uncensored runtime: a timeout
contributes the cutoff only to this capped statistic. Small input samples
have wide uncertainty. These experiments do not establish asymptotic
complexity, nor substitute for soundness/completeness proofs.
When every observed run in a cell is censored, the bootstrap interval for its
capped cost degenerates to the cutoff. That does not prove the population
capped mean equals the cutoff; read it with the nondegenerate completion
interval and the small sample size.

Peak memory is not measured: macOS `/usr/bin/time -l` depends on a sysctl
blocked by this workspace's sandbox. Clock scheduling, frequency scaling,
thermal conditions and other user processes are not controlled. No timings
from Python generation, compilation, or startup are included in the Lean
solver time.
