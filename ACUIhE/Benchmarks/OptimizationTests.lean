import ACUIhE.Solver

namespace OptimizationTests
open ACUIhE
abbrev T := Term Nat Nat Nat
def c (n : Nat) : T := .const n
def x (n : Nat) : T := .var n
def h (n : Nat) (a : T) : T := .hom n a
def e (a : T) : T := .free a
def record (a b : T) : T := e (.add (c 10) (.add (h 0 a) (h 1 b)))

def cases : List (String × Solver.Problem Nat Nat Nat × Bool) :=
  [("binding exposed after its variable was initially undetermined",
      [⟨x 3, x 1⟩, ⟨x 0, c 0⟩,
       ⟨.add (record (x 0) (x 1)) (record (x 1) (x 0)),
        .add (record (c 0) (c 1)) (record (c 1) (c 0))⟩], true),
   ("forced endpoint in an orientation sum",
      [⟨.add (record (c 0) (x 0)) (record (x 0) (c 0)),
        .add (record (c 0) (c 1)) (record (c 1) (c 0))⟩], true),
   ("forced endpoint with reversed summand order",
      [⟨.add (record (c 0) (x 0)) (record (x 0) (c 0)),
        .add (record (c 1) (c 0)) (record (c 0) (c 1))⟩], true),
   ("forced matching across association and nonadjacent duplicates",
      [⟨.add (record (c 0) (x 0)) (.add (e (c 7)) (record (x 0) (c 0))),
        .add (.add (record (c 1) (c 0)) (e (c 7)))
          (.add (record (c 0) (c 1)) (record (c 1) (c 0)))⟩], true),
   ("multiple nonzero summands may match one partner",
      [⟨.add (e (.add (c 0) (x 0))) (e (.add (c 0) (x 1))), e (c 0)⟩], true),
   ("optional unmatched E summand may vanish",
      [⟨.add (e (x 0)) (e (c 0)), e (c 0)⟩], true),
   ("ambiguous E matching retains all choices",
      [⟨.add (e (x 0)) (e (x 1)), .add (e (c 0)) (e (c 1))⟩], true),
   ("exposed variables may absorb E summands",
      [⟨.add (e (c 0)) (x 0), .add (e (c 1)) (x 1)⟩,
       ⟨x 0, e (c 1)⟩, ⟨x 1, e (c 0)⟩], true),
   ("zero E child is not required to match",
      [⟨.add (e .zero) (e (c 0)), e (c 0)⟩], true),
   ("outer projection does not turn nested E into a constant",
      [⟨.add (e (e (c 0))) (e (x 0)), e (e (c 0))⟩], true),
   ("forced match retains an unmatched residual contradiction",
      [⟨.add (e (c 0)) (e (c 2)), .add (e (.add (c 0) (x 0))) (e (c 1))⟩], false),
   ("forced fields retain shared variable conflicts",
      [⟨.add (record (x 0) (x 0)) (record (c 2) (c 2)),
        .add (record (c 0) (c 1)) (record (c 2) (c 2))⟩], false),
   ("idempotent constructor alias", [⟨.add (record (c 0) (c 1)) (record (c 0) (c 1)),
      record (x 0) (x 1)⟩, ⟨x 1, c 1⟩], true),
   ("additive unit constructor alias", [⟨.add .zero (record (c 0) (c 1)), record (x 0) (x 1)⟩], true),
   ("open E children can supply each other's constants",
      [⟨.add (e (.add (c 0) (x 0))) (e (c 3)),
        .add (e (.add (c 1) (x 1))) (e (c 3))⟩], true),
   ("prefixed variables can supply longer constant words",
      [⟨.add (e (h 0 (x 0))) (e (c 0)), .add (e (h 0 (h 1 (c 1)))) (e (c 0))⟩], true),
   ("restore chained bindings", [⟨x 0, x 1⟩, ⟨x 1, e (c 0)⟩, ⟨x 2, h 1 (x 0)⟩], true),
   ("record parameters", [⟨record (x 0) (x 1), record (c 0) (e (c 1))⟩], true),
   ("record shared variable conflict", [⟨record (x 0) (x 0), record (c 0) (c 1)⟩], false),
   ("overlapping homomorphism fields", [⟨.add (h 0 (x 0)) (h 0 (c 0)),
      .add (h 0 (c 1)) (h 0 (x 1))⟩, ⟨x 0, c 1⟩, ⟨x 1, c 0⟩], true),
   ("exposed variables absorb constants", [⟨.add (c 0) (x 0), .add (c 1) (x 1)⟩,
      ⟨x 0, c 1⟩, ⟨x 1, c 0⟩], true),
   ("additive self reference has solutions", [⟨x 0, .add (x 0) (c 0)⟩], true),
   ("growing homomorphism cycle has no finite solution", [⟨x 0, .add (c 0) (h 0 (x 0))⟩], false),
   ("E variable may vanish", [⟨e (x 0), .zero⟩], true),
   ("one E summand may vanish", [⟨.add (e (x 0)) (e (x 1)), e (c 0)⟩,
      ⟨x 0, .zero⟩, ⟨x 1, c 0⟩], true),
   ("equal E summands may merge", [⟨.add (e (x 0)) (e (x 1)), e (c 0)⟩,
      ⟨x 0, c 0⟩, ⟨x 1, c 0⟩], true),
   ("prefixed rigid constant cannot vanish", [⟨e (.add (h 0 (c 0)) (x 0)), .zero⟩], false),
   ("E does not distribute", [⟨e (.add (c 0) (c 1)), .add (e (c 0)) (e (c 1))⟩], false),
   ("homomorphisms do not commute", [⟨h 0 (h 1 (c 0)), h 1 (h 0 (c 0))⟩], false),
   ("ground conflict in an open problem", [⟨x 0, x 1⟩, ⟨e (c 0), e (c 1)⟩], false),
   ("all shared constraints retained", [⟨.add (x 0) (x 1), .add (c 0) (c 1)⟩,
      ⟨x 0, c 0⟩, ⟨x 1, c 1⟩], true)]

def main : IO Unit := do
  for (name, problem, expected) in cases do
    let answer := Solver.isUnifiable problem
    if answer != expected then throw (IO.userError s!"decision mismatch: {name}")
    match Solver.solve problem with
    | none => if expected then throw (IO.userError s!"missing witness: {name}")
    | some iv =>
      if !expected then throw (IO.userError s!"unexpected witness: {name}")
      unless problem.all (fun q => decide
          (q.left.eval Graph.constant iv = q.right.eval Graph.constant iv)) do
        throw (IO.userError s!"invalid original-equation witness: {name}")
    IO.println s!"ok: {name}"

end OptimizationTests

def main : IO Unit := OptimizationTests.main

#print axioms ACUIhE.Solver.solve_sound
#print axioms ACUIhE.Solver.solve_sound_eval
#print axioms ACUIhE.Solver.solve_complete_of_unifier
#print axioms ACUIhE.Solver.solve_none_iff
#print axioms ACUIhE.Solver.isUnifiable_iff
#print axioms ACUIhE.Solver.Elimination.run_unifiable_iff
#print axioms ACUIhE.FILO.Coordinates.defer_eq
#print axioms ACUIhE.Solver.Prepared.required_positive

#print axioms ACUIhE.Solver.Prepared.dependency_order
#print axioms ACUIhE.Solver.compatible_necessary
#print axioms ACUIhE.Solver.ForcedMatching.outer_project
#print axioms ACUIhE.Solver.ForcedMatching.forced_eq
#print axioms ACUIhE.Solver.ForcedMatching.extra_sound
#print axioms ACUIhE.Solver.Decomposition.run_correct
#print axioms ACUIhE.Solver.Elimination.select_progress
