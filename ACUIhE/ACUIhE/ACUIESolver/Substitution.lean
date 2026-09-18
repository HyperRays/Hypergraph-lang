import ACUIhE.Equation

/-!
# Ordinary ACUIE substitution

Substitutions may have arbitrary, possibly nonground ACUIE terms as values.
Composition is simultaneous substitution, not recursive chasing of bindings.
No distributivity, monotonicity, or nonzero assumption on `E` is used.
-/

namespace ACUIhE.ACUIE

universe u v w x y

variable {Const : Type u} {Var : Type v} {Target : Type w} {Next : Type x}

/-- Universal ACUIE equality is sound in any carrier universe. -/
theorem Term.Equal.sound {α : Type y} [ACUIE α] (ic : Const → α) (iv : Var → α)
    {a b : Term Const Var} (h : a.Equal b) : a.eval ic iv = b.eval ic iv := by
  let : _root_.ACUIhE.ACUIhE Empty α := {
    hom := fun r => nomatch r
    free := ACUIE.free
    add_assoc := ACUIE.add_assoc
    add_comm := ACUIE.add_comm
    add_zero := ACUIE.add_zero
    add_idem := ACUIE.add_idem
    hom_add := fun r => nomatch r
    hom_zero := fun r => nomatch r
    free_zero := ACUIE.free_zero
    free_injective := ACUIE.free_injective }
  have eval_eq (t : Term Const Var) :
      (t.toACUIhE (Hom := Empty)).eval ic iv = t.eval ic iv := by
    induction t with
    | zero | const | var => rfl
    | add a b ha hb => exact congrArg₂ (· + ·) ha hb
    | free t ht => exact congrArg (ACUIE.E (α := α)) ht
  have full : _root_.ACUIhE.Term.Equal (a.toACUIhE (Hom := Empty)) b.toACUIhE :=
    (semanticallyEquivalent_iff_toACUIhE a b).mp h
  exact (eval_eq a).symm.trans
    ((_root_.ACUIhE.Term.Equal.sound (Hom := Empty) ic iv full).trans (eval_eq b))

abbrev Substitution (Const : Type u) (Var : Type v) (Target : Type w) :=
  Var → Term Const Target

def Term.substitute (σ : Substitution Const Var Target) : Term Const Var → Term Const Target
  | .zero => .zero
  | .const c => .const c
  | .var v => σ v
  | .add a b => .add (a.substitute σ) (b.substitute σ)
  | .free a => .free (a.substitute σ)

@[simp] theorem Term.eval_substitute {α : Type y} [ACUIE α]
    (σ : Substitution Const Var Target) (ic : Const → α) (iv : Target → α)
    (t : Term Const Var) :
    (t.substitute σ).eval ic iv = t.eval ic (fun v => (σ v).eval ic iv) := by
  induction t <;> simp_all [substitute, eval]

def Substitution.identity : Substitution Const Var Var := Term.var

/-- Apply `σ` first, then `τ` to the variables remaining in its values. -/
def Substitution.compose (σ : Substitution Const Var Target)
    (τ : Substitution Const Target Next) : Substitution Const Var Next :=
  fun v => (σ v).substitute τ

@[simp] theorem Term.substitute_identity (t : Term Const Var) :
    t.substitute Substitution.identity = t := by
  induction t <;> simp_all [substitute, Substitution.identity]

theorem Term.substitute_compose (σ : Substitution Const Var Target)
    (τ : Substitution Const Target Next) (t : Term Const Var) :
    (t.substitute σ).substitute τ = t.substitute (σ.compose τ) := by
  induction t <;> simp_all [substitute, Substitution.compose]

@[simp] theorem Substitution.compose_identity (σ : Substitution Const Var Target) :
    σ.compose identity = σ := by
  funext v
  exact Term.substitute_identity (σ v)

@[simp] theorem Substitution.identity_compose (σ : Substitution Const Var Target) :
    identity.compose σ = σ := rfl

theorem Substitution.compose_assoc {After : Type y} (σ : Substitution Const Var Target)
    (τ : Substitution Const Target Next) (ρ : Substitution Const Next After) :
    (σ.compose τ).compose ρ = σ.compose (τ.compose ρ) := by
  funext v
  exact Term.substitute_compose τ ρ (σ v)

theorem Term.Equal.substitute {a b : Term Const Var} (h : a.Equal b)
    (σ : Substitution Const Var Target) : (a.substitute σ).Equal (b.substitute σ) := by
  intro α _ ic iv
  simp only [eval_substitute]
  exact Term.Equal.sound ic (fun v => (σ v).eval ic iv) h

theorem Term.substitute_congr (σ τ : Substitution Const Var Target)
    (h : ∀ v, (σ v).Equal (τ v)) (t : Term Const Var) :
    (t.substitute σ).Equal (t.substitute τ) := by
  intro α _ ic iv
  simp only [eval_substitute]
  exact congrArg (t.eval ic) (funext fun v => Term.Equal.sound ic iv (h v))

def Term.occurs [DecidableEq Var] (v : Var) : Term Const Var → Bool
  | .zero | .const _ => false
  | .var w => decide (v = w)
  | .add a b => a.occurs v || b.occurs v
  | .free a => a.occurs v

def Substitution.single [DecidableEq Var] (v : Var) (value : Term Const Var) :
    Substitution Const Var Var := fun w => if w = v then value else .var w

/-- An absent variable can be replaced without changing the term at all. -/
theorem Term.substitute_single_of_not_occurs [DecidableEq Var]
    (v : Var) (value t : Term Const Var) (h : t.occurs v = false) :
    t.substitute (Substitution.single v value) = t := by
  induction t with
  | zero | const => rfl
  | var w =>
    have ne : w ≠ v := by simpa [occurs, eq_comm] using h
    simp [substitute, Substitution.single, ne]
  | add a b ha hb =>
    have parts : a.occurs v = false ∧ b.occurs v = false := by simpa [occurs] using h
    simp only [substitute, ha parts.1, hb parts.2]
  | free a ha => exact congrArg Term.free (ha h)

end ACUIhE.ACUIE
