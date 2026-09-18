import ACUIhE.FILO.Preprocessing.FlatteningI
import ACUIhE.FILO.Preprocessing.Columns

/-!
# Executable one-constant projection (§4.3–4.4)

Turn definitions into their two inequalities, replace other constants by
zero, and reduce restrictions of zero. The correctness theorem is an exact
equivalence for each interpretation, including the generated auxiliary names.
-/

namespace ACUIhE.FILO.Projection

universe u v w x

variable {Const : Type u} {Var : Type v} {Hom : Type w}

def constraints (m : Flat.Model Const Var Hom) : List (Generic.Inequality (Flat.Concept Const Var Hom)) :=
  m.inequalities ++ m.definitions.flatMap fun q => [⟨[q.left], [q.right]⟩, ⟨[q.right], [q.left]⟩]

theorem constraints_iff {α : Type x} [ACUIh Hom α]
    (m : Flat.Model Const Var Hom) (ic : Const → α) (iv : Var → α) :
    (∀ q ∈ constraints m, q.Holds (· + ·) (Flat.Concept.eval ic iv)) ↔ m.Holds ic iv := by
  have singleton : ∀ p : Flat.Particle Const Var Hom,
      Flat.Concept.eval ic iv [p] = p.eval ic iv := fun _ => ACUIh.add_zero _
  constructor
  · intro h
    refine ⟨fun q hq => h q (List.mem_append_left _ hq), ?_⟩
    intro q hq
    have forward := h ⟨[q.left], [q.right]⟩ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨q, hq, by simp⟩))
    have backward := h ⟨[q.right], [q.left]⟩ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨q, hq, by simp⟩))
    change Flat.Concept.eval ic iv [q.left] + Flat.Concept.eval ic iv [q.right] = _ at forward
    change Flat.Concept.eval ic iv [q.right] + Flat.Concept.eval ic iv [q.left] = _ at backward
    simp only [singleton] at forward backward
    exact (backward.symm.trans (ACUIh.add_comm _ _)).trans forward
  · rintro ⟨inequalities, definitions⟩ q hq
    rcases List.mem_append.mp hq with old | generated
    · exact inequalities q old
    · obtain ⟨eq, heq, member⟩ := List.mem_flatMap.mp generated
      have same := definitions eq heq
      change eq.left.eval ic iv = eq.right.eval ic iv at same
      rcases List.mem_cons.mp member with rfl | member
      · change Flat.Concept.eval ic iv [eq.left] + Flat.Concept.eval ic iv [eq.right] = _
        rw [singleton, singleton, same]
        exact ACUIh.add_idem _
      · have eq' := List.mem_singleton.mp member
        subst q
        change Flat.Concept.eval ic iv [eq.right] + Flat.Concept.eval ic iv [eq.left] = _
        rw [singleton, singleton, same]
        exact ACUIh.add_idem _

variable [DecidableEq Const]

def atom (c : Const) : Flat.Atom Const Var → Option (Flat.Atom Unit Var)
  | .const d => if d = c then some (.const ()) else none
  | .var v => some (.var v)

def particle (c : Const) : Flat.Particle Const Var Hom → Option (Flat.Particle Unit Var Hom)
  | .atom a => (atom c a).map .atom
  | .hom r a => (atom c a).map (.hom r)

def concept (c : Const) (ps : Flat.Concept Const Var Hom) : Flat.Concept Unit Var Hom :=
  ps.filterMap (particle c)

def compile (m : Flat.Model Const Var Hom) (c : Const) : Flat.Model Unit Var Hom where
  inequalities := (constraints m).map fun q => ⟨concept c q.left, concept c q.right⟩
  definitions := []

section Semantics

variable {α : Type x} [ACUIh Hom α]

theorem particle_eval (c : Const) (a : α) (iv : Var → α) (p : Flat.Particle Const Var Hom) :
    ((particle c p).map (Flat.Particle.eval (fun _ => a) iv)).getD 0 =
      p.eval (fun d => if d = c then a else 0) iv := by
  cases p with
  | atom p =>
    cases p with
    | var v => rfl
    | const d => by_cases eq : d = c <;> simp [particle, atom, eq, Flat.Particle.eval, Flat.Atom.eval]
  | hom r p =>
    cases p with
    | var v => rfl
    | const d =>
      by_cases eq : d = c <;>
        simp [particle, atom, eq, Flat.Particle.eval, Flat.Atom.eval, ACUIh.H, ACUIh.hom_zero]

theorem concept_eval (c : Const) (a : α) (iv : Var → α) (ps : Flat.Concept Const Var Hom) :
    Flat.Concept.eval (fun _ => a) iv (concept c ps) =
      ps.eval (fun d => if d = c then a else 0) iv := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    have head := particle_eval c a iv p
    cases projected : particle c p with
    | none =>
      simp only [projected, Option.map_none, Option.getD_none] at head
      change Flat.Concept.eval (fun _ => a) iv
        ((p :: rest).filterMap (particle c)) = _ + _
      rw [List.filterMap_cons, projected]
      change Flat.Concept.eval (fun _ => a) iv (concept c rest) = _ + _
      rw [ih, ← head, ACUIh.add_comm, ACUIh.add_zero]
    | some q =>
      simp only [projected, Option.map_some, Option.getD_some] at head
      change Flat.Concept.eval (fun _ => a) iv
        ((p :: rest).filterMap (particle c)) = _ + _
      rw [List.filterMap_cons, projected]
      change q.eval (fun _ => a) iv + Flat.Concept.eval (fun _ => a) iv (concept c rest) = _ + _
      rw [head, ih]

/-- Projection is exact; it does not need a guessed substitution to run. -/
theorem holds_compile_iff (m : Flat.Model Const Var Hom) (c : Const) (a : α) (iv : Var → α) :
    (compile m c).Holds (fun _ => a) iv ↔ m.Holds (fun d => if d = c then a else 0) iv := by
  rw [← constraints_iff m (fun d => if d = c then a else 0) iv]
  change ((∀ q ∈ (constraints m).map (fun q =>
      (⟨concept c q.left, concept c q.right⟩ : Generic.Inequality _)),
      q.Holds (· + ·) (Flat.Concept.eval (fun _ => a) iv)) ∧
      (∀ q ∈ ([] : List (Generic.Equation (Flat.Particle Unit Var Hom))),
        q.Holds (Flat.Particle.eval (fun _ => a) iv))) ↔ _
  simp only [List.forall_mem_map, Generic.Inequality.Holds, concept_eval]
  exact ⟨And.left, fun h => ⟨h, by simp⟩⟩

theorem solvable_compile_iff (m : Flat.Model Const Var Hom) (c : Const) (a : α) :
    (compile m c).Solvable (fun _ => a) ↔ m.Solvable (fun d => if d = c then a else 0) := by
  unfold Flat.Model.Solvable
  exact exists_congr (holds_compile_iff m c a)

end Semantics

variable [DecidableEq Var] [DecidableEq Hom]

local instance : ACUIh Hom (ACUIh.Linear.WordPolynomial Hom) := Column.algebra

/-- The first two executable transformations composed with the matrix contract. -/
theorem unifiable_iff (p : Problem Const Var Hom) :
    p.Unifiable ↔ ∀ c ∈ p.constantNames,
      (compile (FlatteningI.compile p) c).Solvable
        (fun _ => (1 : ACUIh.Linear.WordPolynomial Hom)) := by
  rw [Column.unifiable_iff]
  apply forall_congr'
  intro c
  apply forall_congr'
  intro _
  rw [solvable_compile_iff, FlatteningI.solvable_compile_iff]
  rfl

end ACUIhE.FILO.Projection
