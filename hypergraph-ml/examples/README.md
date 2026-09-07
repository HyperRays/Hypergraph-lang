# Hypergraph language examples

Every `.hg` file in this directory is a complete document that can be run
from `hypergraph-ml`:

```sh
./tools/run.sh examples/heterogeneous_sets.hg
```

The runnable examples normally omit `let` annotations and allow whole-file
type inference to determine their types. An annotation is retained only when
it requests behavior that cannot be inferred, such as mutability or an
explicit edge coercion.

- `basic.hg` builds a minimal person graph.
- `heterogeneous_sets.hg` shows where sum types are constructible.
- `lists.hg` demonstrates ordered, duplicate-preserving homogeneous,
  heterogeneous, nested, and payload lists.
- `nested_inference.hg` combines three-parameter enums, nested generic structs,
  aliases, sets, and cross-binding refinement.
- `inferred_network_schema.hg` infers a generic graph schema from mixed edge
  kinds and partially constrained enum constructors.
- `social_graph.hg` combines directed and undirected hyperedges.
- `set_operations.hg` demonstrates immutable and mutable set operations.
- `generic_data.hg` exercises generic structs, enums, aliases, and inference.

The files under `rejected/` are intentional type errors. Running one should
print the documented diagnostic and exit with a non-zero status. They are
useful as small negative examples rather than executable demonstrations.
