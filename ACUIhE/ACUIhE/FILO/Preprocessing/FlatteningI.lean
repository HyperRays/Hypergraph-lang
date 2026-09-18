import ACUIhE.FILO.Preprocessing.Flat

/-!
# Verified flattening I (§4.2, Lemma 3)

Distribute restrictions over sums, name restricted atoms when they become
nested, and retain their defining equations. The algorithm is structurally
recursive and returns only data. Its extension and restriction theorems hold
in every ACUIh algebra, not merely in the ground normal-form model.
-/

namespace ACUIhE.FILO.FlatteningI

open ACUIh Flat

universe u v w x

structure Result (Const : Type u) (Var : Type v) (Hom : Type w) where
  body : Flat.Concept Const (Flat.Variable Const Var Hom) Hom
  definitions : List (Generic.Equation (Flat.Particle Const (Flat.Variable Const Var Hom) Hom))

variable {Const : Type u} {Var : Type v} {Hom : Type w}

def term : ACUIh.Term Const Var Hom → Result Const Var Hom
  | .zero => ⟨[], []⟩
  | .const c => ⟨[.atom (.const c)], []⟩
  | .var v => ⟨[.atom (.var (.user v))], []⟩
  | .add a b =>
    let left := term a
    let right := term b
    ⟨left.body ++ right.body, left.definitions ++ right.definitions⟩
  | .hom r t =>
    let child := term t
    ⟨child.body.map (fun p => .hom r p.abstract),
      child.definitions ++ child.body.flatMap Flat.Particle.definitions⟩

def compile (p : Problem Const Var Hom) : Flat.Model Const (Flat.Variable Const Var Hom) Hom where
  inequalities := p.map fun q => ⟨(term q.left).body, (term q.right).body⟩
  definitions := p.flatMap fun q => (term q.left).definitions ++ (term q.right).definitions

section Semantics

variable {α : Type x} [ACUIh Hom α]

/-- Defining equations are sufficient to recover the original interpretation. -/
theorem term_sound (t : ACUIh.Term Const Var Hom) (ic : Const → α)
    (iv : Flat.Variable Const Var Hom → α)
    (defined : ∀ q ∈ (term t).definitions, q.Holds (Flat.Particle.eval ic iv)) :
    (term t).body.eval ic iv = t.eval ic (fun v => iv (.user v)) := by
  induction t with
  | zero => rfl
  | const c => exact ACUIh.add_zero _
  | var v => exact ACUIh.add_zero _
  | add a b ia ib =>
    have da : ∀ q ∈ (term a).definitions, q.Holds (Flat.Particle.eval ic iv) :=
      fun q hq => defined q (List.mem_append_left _ hq)
    have db : ∀ q ∈ (term b).definitions, q.Holds (Flat.Particle.eval ic iv) :=
      fun q hq => defined q (List.mem_append_right _ hq)
    change Flat.Concept.eval ic iv ((term a).body ++ (term b).body) = _ + _
    rw [Flat.Concept.eval_append, ia da, ib db]
  | hom r t ih =>
    have dt : ∀ q ∈ (term t).definitions, q.Holds (Flat.Particle.eval ic iv) :=
      fun q hq => defined q (List.mem_append_left _ hq)
    have ds : ∀ a ∈ (term t).body, ∀ q ∈ a.definitions, q.Holds (Flat.Particle.eval ic iv) :=
      fun a ha q hq => defined q (List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, hq⟩))
    change Flat.Concept.eval ic iv ((term t).body.map (fun p => Flat.Particle.hom r p.abstract)) = ACUIh.H r _
    rw [Flat.Concept.eval_restrict ic iv r _ ds, ih dt]

/-- All generated defining equations hold under the explicit extension. -/
theorem term_definitions (t : ACUIh.Term Const Var Hom) (ic : Const → α) (iv : Var → α) :
    ∀ q ∈ (term t).definitions, q.Holds (Flat.Particle.eval ic (Flat.extend ic iv)) := by
  induction t with
  | zero | const | var => simp [term]
  | add a b ia ib =>
    intro q hq
    rcases List.mem_append.mp hq with ha | hb
    · exact ia q ha
    · exact ib q hb
  | hom r t ih =>
    intro q hq
    rcases List.mem_append.mp hq with old | new
    · exact ih q old
    · obtain ⟨a, _, ha⟩ := List.mem_flatMap.mp new
      exact Flat.Particle.definitions_extend ic iv a q ha

@[simp] theorem term_complete (t : ACUIh.Term Const Var Hom) (ic : Const → α) (iv : Var → α) :
    (term t).body.eval ic (Flat.extend ic iv) = t.eval ic iv :=
  term_sound t ic (Flat.extend ic iv) (term_definitions t ic iv)

/-- The compiled model's definitions imply exactly the original inequalities. -/
theorem compile_sound (p : Problem Const Var Hom) (ic : Const → α)
    (iv : Flat.Variable Const Var Hom → α) (solution : (compile p).Holds ic iv) :
    p.Holds ic (fun v => iv (.user v)) := by
  intro q hq
  have dl : ∀ e ∈ (term q.left).definitions, e.Holds (Flat.Particle.eval ic iv) := by
    intro e he
    exact solution.2 e (List.mem_flatMap.mpr ⟨q, hq, List.mem_append_left _ he⟩)
  have dr : ∀ e ∈ (term q.right).definitions, e.Holds (Flat.Particle.eval ic iv) := by
    intro e he
    exact solution.2 e (List.mem_flatMap.mpr ⟨q, hq, List.mem_append_right _ he⟩)
  have flat := solution.1 ⟨(term q.left).body, (term q.right).body⟩ (List.mem_map.mpr ⟨q, hq, rfl⟩)
  change (term q.left).body.eval ic iv + (term q.right).body.eval ic iv =
    (term q.right).body.eval ic iv at flat
  change q.left.eval ic (fun v => iv (.user v)) + q.right.eval ic (fun v => iv (.user v)) = _
  simpa only [term_sound q.left ic iv dl, term_sound q.right ic iv dr] using flat

/-- Every input solution extends to a solution of the actual compiled model. -/
theorem compile_complete (p : Problem Const Var Hom) (ic : Const → α) (iv : Var → α)
    (solution : p.Holds ic iv) : (compile p).Holds ic (Flat.extend ic iv) := by
  constructor
  · intro q hq
    obtain ⟨original, member, rfl⟩ := List.mem_map.mp hq
    change (term original.left).body.eval ic (Flat.extend ic iv) +
      (term original.right).body.eval ic (Flat.extend ic iv) = _
    simpa only [term_complete, ACUIh.Inequality.Holds, Generic.Inequality.Holds] using solution original member
  · intro q hq
    obtain ⟨original, _, member⟩ := List.mem_flatMap.mp hq
    rcases List.mem_append.mp member with left | right
    · exact term_definitions original.left ic iv q left
    · exact term_definitions original.right ic iv q right

/-- Lemma 3, with no well-formedness or intermediate-correctness assumptions. -/
theorem solvable_compile_iff (p : Problem Const Var Hom) (ic : Const → α) :
    (compile p).Solvable ic ↔ p.Solvable ic := by
  constructor
  · rintro ⟨iv, solution⟩
    exact ⟨fun v => iv (.user v), compile_sound p ic iv solution⟩
  · rintro ⟨iv, solution⟩
    exact ⟨Flat.extend ic iv, compile_complete p ic iv solution⟩

end Semantics

variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]

local instance : ACUIh Hom (NF Const Empty Hom) := NF.algebra

/-- Flattening preserves and reflects the existing matrix-based unifiability. -/
theorem unifiable_iff (p : Problem Const Var Hom) :
    p.Unifiable ↔ (compile p).Solvable (Problem.constants (Hom := Hom)) :=
  (p.unifiable_iff_solvable).trans (solvable_compile_iff p Problem.constants).symm

end ACUIhE.FILO.FlatteningI
