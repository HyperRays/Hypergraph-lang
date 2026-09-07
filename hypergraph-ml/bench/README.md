# Type-inference benchmark

This benchmark measures `Check.check` with an already parsed syntax tree, and
also measures `Driver.parse` followed by `Check.check` for comparison. It uses
15 warmed samples, automatically batches fast cases, and reports per-operation
latency and allocation as CSV.

The workloads are:

- `simple_bindings`: independent inferred integer bindings;
- `generic_chain`: one connected chain of generic constraints refined to
  `Int` through its first node;
- `wide_set`: a heterogeneous set whose element sum contains one distinct
  struct type per item.
- `solver_chain`: a lower-level control with the same `2n + 1` equality shape
  as `generic_chain`, sent directly to the verified solver.

Build the executable using the normal helper, then provide one or more
`WORKLOAD:SIZE` arguments:

```sh
./tools/build.sh --profile release bench/type_inference_bench.exe
./_build/default/bench/type_inference_bench.exe \
  simple_bindings:100 generic_chain:100 wide_set:100
```

Pass `--inference-only` before the workloads to omit the comparative
parse-and-check measurements. This is useful for large generic constraint
graphs.

Committed result files record the platform and date in their filename.
