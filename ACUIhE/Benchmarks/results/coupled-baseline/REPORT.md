# Large coupled-system feasibility probe

Measured the unchanged full ACUIhE solver, including canonical preprocessing.
Executable SHA-256:
`37e246c2aadff2983c11819ce1da9ae1c29d7b9d560f85e6252ba2f0096e3c20`.

These are six deliberately simple connected families at 100 and 200 equations,
not a statistical sample of general workloads. Every original equation is
distinct and nontrivial under term normalization. The variable-incidence graph
is connected; the generated cases are not independent problems concatenated
together. Chains have N-1 variables; cycles have N variables.

## Inputs

Indices in cycles are taken modulo N. All SAT cases have the explicit solution
mapping every variable to the constant a. The existing independent ground
normalizer checks this solution before timing; it is not used by the solver.

- SAT chain: X_i = X_(i+1), with both endpoints fixed to a.
- UNSAT chain: the same chain, with one endpoint fixed to a and the other to b.
  Transitivity would force distinct free constants a and b to be equal.
- Union cycle: X_i + X_(i+1) = a.
- Homomorphism cycle: h_0(X_i) + X_(i+1) = h_0(a) + a.
- E cycle: E(X_i) + X_(i+1) = E(a) + a.
- Mixed cycle: h_0(X_i) + E(X_(i+1)) = h_0(a) + E(a).

## Primary probe

Three fresh-process decision runs per input, reproducibly shuffled serial job
order, five-second post-handshake wall limit. Parsing and process startup are
outside the timed region. Repetitions are the same input, not independent
workload samples. Times below are internal solver medians where all runs finish.

| Family | 100 equations | 200 equations |
|---|---|---|
| SAT chain | 0/3 completed | 0/3 completed |
| UNSAT chain | 0/3 completed | 0/3 completed |
| Union cycle | 0/3 completed | 0/3 completed |
| Homomorphism cycle | 3/3 completed; 3.428 s median | 0/3 completed |
| E cycle | 0/3 completed | 0/3 completed |
| Mixed cycle | 0/3 completed | 0/3 completed |

All non-completions were timeouts, not crashes or UNSAT answers. No completed
answer disagreed with its expected label. Homomorphism-cycle times at N=100
were 3.405, 3.428, and 3.460 seconds.

## Selected longer and extraction checks

One fresh run each, 30-second wall limit; these are selected follow-ups, not a
rerun of the whole cohort. The observed successful family was selected for the
larger-size and witness checks.

| Input | Operation | Result |
|---|---|---|
| Homomorphism cycle, 100 equations/variables | Solve and traverse every variable's graph | SAT, 3.896 s; total graph weight 100 |
| Homomorphism cycle, 200 equations/variables | Decision | SAT, 24.211 s |
| SAT chain, 100 equations/99 variables | Decision | Timeout at 30 s |
| E cycle, 100 equations/variables | Decision | Timeout at 30 s |

Thus 100+ genuinely coupled equations can complete, including actual witness
extraction at 100 variables. These measurements do not establish broadly
practical performance: even simple sparse chains and shallow E cycles can
exceed 30 seconds. No asymptotic complexity follows from these few sizes and
families. Host load and thermal state are uncontrolled. No solver definitions
or proofs were changed for this probe.

## Reproduction and raw records

- [Primary driver](probe.py), [selected follow-up driver](longer.py)
- [Complete inputs and mathematical labels](cases.json)
- [Primary metadata](metadata.json), [primary runs](runs.jsonl), [summary](summary.json)
- [Follow-up metadata](longer-metadata.json), [follow-up runs](longer-runs.jsonl)

Copy both drivers into a fresh output directory before rerunning: they refuse
to overwrite an existing run log. They reuse the existing compiled benchmark
executable and its process/handshake measurement procedure.
