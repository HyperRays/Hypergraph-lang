import ACUIhE.FILO.Problem
import ACUIhE.ACUIhNF.linear.Semantics

/-!
# The output language of flattening I (§4.2)

One value restriction may surround an atom. Auxiliary variable names encode
the nonempty word and generator they abstract; they are names, not nested
operators in the output language. They cannot coincide with user variables.
-/

namespace ACUIhE.FILO.Flat

open ACUIh

universe u v w x

inductive Variable (Const : Type u) (Var : Type v) (Hom : Type w) where
  | user : Var → Variable Const Var Hom
  | aux : Hom → List Hom → Particle Const Var → Variable Const Var Hom
  deriving DecidableEq

abbrev Atom (Const : Type u) (Var : Type v) := ACUIh.Particle Const Var

inductive Particle (Const : Type u) (Var : Type v) (Hom : Type w) where
  | atom : Atom Const Var → Particle Const Var Hom
  | hom : Hom → Atom Const Var → Particle Const Var Hom
  deriving DecidableEq

abbrev Concept (Const : Type u) (Var : Type v) (Hom : Type w) := List (Particle Const Var Hom)

structure Model (Const : Type u) (Var : Type v) (Hom : Type w) where
  inequalities : List (Generic.Inequality (Concept Const Var Hom))
  definitions : List (Generic.Equation (Particle Const Var Hom))

variable {Const : Type u} {Var : Type v} {Hom : Type w}

def Atom.source : Atom Const (Variable Const Var Hom) → Summand Const Var Hom
  | .const c => ([], .const c)
  | .var (.user v) => ([], .var v)
  | .var (.aux r word p) => (r :: word, p)

/-- The variable naming one value restriction of this atom. -/
def Atom.name (r : Hom) (a : Atom Const (Variable Const Var Hom)) : Variable Const Var Hom :=
  .aux r a.source.1 a.source.2

def Particle.abstract : Particle Const (Variable Const Var Hom) Hom → Atom Const (Variable Const Var Hom)
  | .atom a => a
  | .hom r a => .var (a.name r)

/-- Abstracting a restriction introduces its defining equality. -/
def Particle.definitions : Particle Const (Variable Const Var Hom) Hom →
    List (Generic.Equation (Particle Const (Variable Const Var Hom) Hom))
  | .atom _ => []
  | .hom r a => [⟨.atom (.var (a.name r)), .hom r a⟩]

section Semantics

variable {α : Type x} [ACUIh Hom α]

def Atom.eval (ic : Const → α) (iv : Var → α) : Atom Const Var → α
  | .const c => ic c
  | .var v => iv v

def Particle.eval (ic : Const → α) (iv : Var → α) : Particle Const Var Hom → α
  | .atom a => a.eval ic iv
  | .hom r a => ACUIh.H r (a.eval ic iv)

def Concept.eval (ic : Const → α) (iv : Var → α) : Concept Const Var Hom → α
  | [] => 0
  | p :: rest => p.eval ic iv + Concept.eval ic iv rest

def Model.Holds (m : Model Const Var Hom) (ic : Const → α) (iv : Var → α) : Prop :=
  (∀ q ∈ m.inequalities, q.Holds (· + ·) (Concept.eval ic iv)) ∧
    ∀ q ∈ m.definitions, q.Holds (Particle.eval ic iv)

def Model.Solvable (m : Model Const Var Hom) (ic : Const → α) : Prop := ∃ iv, m.Holds ic iv

/-- Canonical extension of an interpretation to the auxiliary names. -/
def extend (ic : Const → α) (iv : Var → α) : Variable Const Var Hom → α
  | .user v => iv v
  | .aux r word p => Linear.evalWord (r :: word) ((p.reify (Hom := Hom)).eval ic iv)

@[simp] theorem extend_user (ic : Const → α) (iv : Var → α) (v : Var) :
    extend (Hom := Hom) ic iv (.user v) = iv v := rfl

theorem Atom.eval_source (ic : Const → α) (iv : Var → α) (a : Atom Const (Variable Const Var Hom)) :
    Linear.evalWord a.source.1 ((a.source.2.reify (Hom := Hom)).eval ic iv) = a.eval ic (extend ic iv) := by
  cases a with
  | const c => rfl
  | var v => cases v <;> rfl

@[simp] theorem extend_name (ic : Const → α) (iv : Var → α) (r : Hom) (a : Atom Const (Variable Const Var Hom)) :
    extend ic iv (a.name r) = ACUIh.H r (a.eval ic (extend ic iv)) := by
  change ACUIh.H r (Linear.evalWord a.source.1 ((a.source.2.reify (Hom := Hom)).eval ic iv)) = _
  rw [Atom.eval_source]

theorem Particle.definitions_extend (ic : Const → α) (iv : Var → α) (p : Particle Const (Variable Const Var Hom) Hom) :
    ∀ q ∈ p.definitions, q.Holds (Particle.eval ic (extend ic iv)) := by
  cases p with
  | atom a => simp [definitions]
  | hom r a => simp [definitions, Generic.Equation.Holds, eval, Atom.eval]

theorem Particle.eval_abstract (ic : Const → α) (iv : Variable Const Var Hom → α)
    (p : Particle Const (Variable Const Var Hom) Hom)
    (defined : ∀ q ∈ p.definitions, q.Holds (Particle.eval ic iv)) :
    p.abstract.eval ic iv = p.eval ic iv := by
  cases p with
  | atom a => rfl
  | hom r a => exact defined _ (List.mem_singleton_self _)

@[simp] theorem Concept.eval_append (ic : Const → α) (iv : Var → α)
    (a b : Concept Const Var Hom) : Concept.eval ic iv (a ++ b) = a.eval ic iv + b.eval ic iv := by
  induction a with
  | nil => exact ((ACUIh.add_comm _ _).trans (ACUIh.add_zero _)).symm
  | cons p rest ih =>
    change p.eval ic iv + Concept.eval ic iv (rest ++ b) = _
    rw [ih]
    exact (ACUIh.add_assoc _ _ _).symm

theorem Concept.eval_restrict (ic : Const → α) (iv : Variable Const Var Hom → α)
    (r : Hom) (ps : Concept Const (Variable Const Var Hom) Hom)
    (defined : ∀ p ∈ ps, ∀ q ∈ p.definitions, q.Holds (Particle.eval ic iv)) :
    Concept.eval ic iv (ps.map (fun p => Particle.hom r p.abstract)) = ACUIh.H r (ps.eval ic iv) := by
  induction ps with
  | nil => exact (ACUIh.hom_zero r).symm
  | cons p rest ih =>
    change ACUIh.H r (p.abstract.eval ic iv) + _ = ACUIh.H r (p.eval ic iv + _)
    rw [Particle.eval_abstract ic iv p (defined p (by simp)),
      ih (fun p hp => defined p (by simp [hp]))]
    exact (ACUIh.hom_add r _ _).symm

end Semantics

end ACUIhE.FILO.Flat
