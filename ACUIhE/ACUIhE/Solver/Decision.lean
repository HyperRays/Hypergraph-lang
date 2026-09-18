import ACUIhE.Solver.Preparation
import ACUIhE.Solver.Projection
import ACUIhE.Solver.Reconstruction
import ACUIhE.Solver.Elimination

/-! # Sound and complete full-signature unification -/

namespace ACUIhE.Solver

universe u v w x
variable {Const : Type u} {Var : Type v} {Hom : Type w} {Target : Type x}
variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]

namespace Prepared

def solve (p : Prepared Const Var Hom) : Option (Var → Graph Const Empty Hom) :=
  p.search.map (fun result => p.assignment result.2 Graph.constant)

theorem solve_sound (p : Prepared Const Var Hom) {σ : Var → Graph Const Empty Hom}
    (found : p.solve = some σ) : p.Holds Graph.constant σ := by
  obtain ⟨result, search_found, rfl⟩ := Option.map_eq_some_iff.mp found
  exact p.reconstruction_sound result.1 result.2 (p.search_sound search_found) Graph.constant

theorem solve_complete (p : Prepared Const Var Hom) (h : p.Unifiable) :
    ∃ σ, p.solve = some σ := by
  obtain ⟨iv, solution⟩ := h
  obtain ⟨labels, m, valid⟩ := p.matching_of_solution iv solution
  obtain ⟨result, found⟩ := p.search_complete labels m valid
  exact ⟨p.assignment result.2 Graph.constant, by simp only [solve, found, Option.map_some]⟩

theorem solve_none_iff (p : Prepared Const Var Hom) : p.solve = none ↔ ¬ p.Unifiable := by
  constructor
  · intro failed solution
    obtain ⟨σ, found⟩ := p.solve_complete solution
    rw [failed] at found
    cases found
  · intro no
    cases found : p.solve with
    | none => rfl
    | some σ => exact (no ⟨σ, p.solve_sound found⟩).elim

end Prepared

namespace Residual

/-- Solve the residual coupled problem after deterministic simplification. -/
def solve (p : Problem Const Var Hom) : Option (Var → Graph Const Empty Hom) :=
  (Preparation.compile p).solve.map (fun σ v => σ (.inl v))

theorem solve_sound (p : Problem Const Var Hom) {σ : Var → Graph Const Empty Hom}
    (found : solve p = some σ) : p.IsSolution σ := by
  obtain ⟨iv, prepared_found, rfl⟩ := Option.map_eq_some_iff.mp found
  exact Preparation.compile_sound p Graph.constant iv ((Preparation.compile p).solve_sound prepared_found)

/-- The returned graph substitution solves the input under interpretation in
every full algebra, not just in the canonical graph model. -/
theorem solve_sound_eval {α : Type x} [ACUIhE Hom α]
    (p : Problem Const Var Hom) {σ : Var → Graph Const Empty Hom}
    (found : solve p = some σ) (ic : Const → α) :
    p.Holds ic (fun v => Graph.eval ic Empty.elim (σ v)) := by
  intro q hq
  change q.left.eval ic _ = q.right.eval ic _
  rw [← Problem.eval_graph ic σ q.left, ← Problem.eval_graph ic σ q.right]
  exact congrArg (Graph.eval ic Empty.elim) (solve_sound p found q hq)

theorem solve_complete (p : Problem Const Var Hom) (h : p.Unifiable) :
    ∃ σ, solve p = some σ := by
  obtain ⟨iv, solution⟩ := (p.unifiable_iff_graph).mp h
  have prepared : (Preparation.compile p).Unifiable :=
    ⟨Preparation.extend Graph.constant iv, Preparation.compile_complete p Graph.constant iv solution⟩
  obtain ⟨σ, found⟩ := (Preparation.compile p).solve_complete prepared
  exact ⟨fun v => σ (.inl v), by simp only [solve, found, Option.map_some]⟩

/-- Completeness starts with any ordinary unifier, including nonground
substitutions over an arbitrary target-variable type. -/
theorem solve_complete_of_unifier (p : Problem Const Var Hom)
    (σ : Var → Term Const Target Hom) (h : p.IsUnifier σ) : ∃ result, solve p = some result :=
  solve_complete p (p.unifiable_of_solution _ (p.solution_of_unifier σ h))

theorem solve_none_iff (p : Problem Const Var Hom) : solve p = none ↔ ¬ p.Unifiable := by
  constructor
  · intro failed solution
    obtain ⟨σ, found⟩ := solve_complete p solution
    rw [failed] at found
    cases found
  · intro no
    cases found : solve p with
    | none => rfl
    | some σ => exact (no (p.unifiable_of_solution σ (solve_sound p found))).elim

/-- Decision-only entry point: do not reconstruct E graphs. -/
def isUnifiable (p : Problem Const Var Hom) : Bool := (Preparation.compile p).searchDeferred.isSome

theorem isUnifiable_iff (p : Problem Const Var Hom) : isUnifiable p = true ↔ p.Unifiable := by
  have same : (solve p).isSome = isUnifiable p := by
    simp only [solve, Prepared.solve, Prepared.search, Option.isSome_map, isUnifiable]
  rw [← same]
  cases found : solve p with
  | none => simp [show ¬ p.Unifiable from (solve_none_iff p).mp found]
  | some σ => simp [show p.Unifiable from p.unifiable_of_solution σ (solve_sound p found)]

end Residual

/-- Simplification preserves solvability and records every eliminated binding. -/
def solve (p : Problem Const Var Hom) : Option (Var → Graph Const Empty Hom) :=
  let r := Elimination.run p
  if Elimination.groundCheck r.problem then (Residual.solve r.problem).map r.restore else none

theorem solve_sound (p : Problem Const Var Hom) {σ : Var → Graph Const Empty Hom}
    (found : solve p = some σ) : p.IsSolution σ := by
  dsimp only [solve] at found
  split_ifs at found with check
  · obtain ⟨iv, solved, rfl⟩ := Option.map_eq_some_iff.mp found
    exact Elimination.run_sound p iv (Residual.solve_sound _ solved)

theorem solve_sound_eval {α : Type x} [ACUIhE Hom α]
    (p : Problem Const Var Hom) {σ : Var → Graph Const Empty Hom}
    (found : solve p = some σ) (ic : Const → α) :
    p.Holds ic (fun v => Graph.eval ic Empty.elim (σ v)) := by
  intro q hq
  change q.left.eval ic _ = q.right.eval ic _
  rw [← Problem.eval_graph ic σ q.left, ← Problem.eval_graph ic σ q.right]
  exact congrArg (Graph.eval ic Empty.elim) (solve_sound p found q hq)

theorem solve_complete (p : Problem Const Var Hom) (h : p.Unifiable) :
    ∃ σ, solve p = some σ := by
  obtain ⟨iv, valid⟩ := p.unifiable_iff_graph.mp h
  have reduced := Elimination.run_complete p iv valid
  have check := Elimination.groundCheck_complete _ iv reduced
  obtain ⟨σ, found⟩ := Residual.solve_complete _ (Problem.unifiable_of_solution _ iv reduced)
  exact ⟨(Elimination.run p).restore σ, by simp only [solve, check, if_true, found, Option.map_some]⟩

theorem solve_complete_of_unifier (p : Problem Const Var Hom)
    (σ : Var → Term Const Target Hom) (h : p.IsUnifier σ) : ∃ result, solve p = some result :=
  solve_complete p (p.unifiable_of_solution _ (p.solution_of_unifier σ h))

theorem solve_none_iff (p : Problem Const Var Hom) : solve p = none ↔ ¬ p.Unifiable := by
  constructor
  · intro failed valid
    obtain ⟨σ, found⟩ := solve_complete p valid
    rw [failed] at found
    cases found
  · intro absent
    cases found : solve p with
    | none => rfl
    | some σ => exact (absent (p.unifiable_of_solution σ (solve_sound p found))).elim

/-- The Boolean API applies the same exact simplification and ground rejection. -/
def isUnifiable (p : Problem Const Var Hom) : Bool :=
  let q := (Elimination.run p).problem
  Elimination.groundCheck q && Residual.isUnifiable q

theorem isUnifiable_iff (p : Problem Const Var Hom) : isUnifiable p = true ↔ p.Unifiable := by
  simp only [isUnifiable, Bool.and_eq_true, Residual.isUnifiable_iff]
  constructor
  · exact fun h => (Elimination.run_unifiable_iff p).mp h.2
  · intro h
    have reduced := (Elimination.run_unifiable_iff p).mpr h
    obtain ⟨iv, valid⟩ := Problem.unifiable_iff_graph _ |>.mp reduced
    exact ⟨Elimination.groundCheck_complete _ iv valid, reduced⟩

instance (p : Problem Const Var Hom) : Decidable p.Unifiable :=
  decidable_of_iff (isUnifiable p = true) (isUnifiable_iff p)

end ACUIhE.Solver
