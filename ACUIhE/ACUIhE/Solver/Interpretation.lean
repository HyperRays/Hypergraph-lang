import ACUIhE.Solver.Search

/-! # Interpretation of word-valued rows in a full algebra -/

namespace ACUIhE.Solver

open ACUIh.Linear

universe u v w x
variable {Const : Type u} {Var : Type v} {Hom : Type w} {α : Type x}
variable [DecidableEq Const] [DecidableEq Hom] [ACUIh Hom α]

local instance : Std.Associative (fun a b : α => a + b) := ⟨ACUIh.add_assoc (Hom := Hom)⟩
local instance : Std.Commutative (fun a b : α => a + b) := ⟨ACUIh.add_comm (Hom := Hom)⟩

def decode (ic : Const → α) (nf : ACUIh.NF Const Empty Hom) : α :=
  ACUIh.NF.eval ic Empty.elim nf

omit [DecidableEq Const] [DecidableEq Hom] in
@[simp] theorem decode_zero (ic : Const → α) : decode (Hom := Hom) ic ∅ = 0 := rfl

theorem decode_instantiate (ic : Const → α) (m : GroundMatrix Const Var Hom)
    (t : ACUIh.Term Const Var Hom) :
    decode ic (instantiateNF m t) = t.eval ic (fun v => decode ic (m v).toNF) := by
  induction t with
  | zero | var => rfl
  | const => simp [decode, instantiateNF, ACUIh.Summand.reify, ACUIh.Particle.reify,
      ACUIh.reifyWord, ACUIh.Term.eval]
  | add a b ia ib => simpa only [instantiateNF, decode, ACUIh.NF.eval_union, ACUIh.Term.eval] using congrArg₂ (· + ·) ia ib
  | hom h t ih => simpa only [instantiateNF, decode, ACUIh.NF.eval_prepend, ACUIh.Term.eval] using congrArg (ACUIh.H h) ih

omit [DecidableEq Const] [DecidableEq Hom] in
theorem decode_congr (a b : Const → α) (nf : ACUIh.NF Const Empty Hom)
    (same : ∀ word c, (word, ACUIh.Particle.const c) ∈ nf → a c = b c) :
    decode a nf = decode b nf := by
  unfold decode ACUIh.NF.eval
  apply Finset.fold_congr
  intro s hs
  obtain ⟨word, particle⟩ := s
  cases particle with
  | var v => exact Empty.elim v
  | const c =>
    have equal := same word c hs
    change (ACUIh.reifyWord word (.const c)).eval a Empty.elim =
      (ACUIh.reifyWord word (.const c)).eval b Empty.elim
    clear hs same
    induction word with
    | nil => exact equal
    | cons h word ih => exact congrArg (ACUIh.H h) ih

theorem coefficient_ne_zero_of_mem (nf : ACUIh.NF Const Empty Hom) (word : List Hom) (c : Const)
    (member : (word, ACUIh.Particle.const c) ∈ nf) : Row.ofNF nf c ≠ 0 := by
  intro zero
  have present := (mem_coefficient nf (.const c) word).mpr member
  change word ∈ (Row.ofNF nf c).words at present
  simp [zero] at present

theorem decode_names {n : Nat} (ic : Const ⊕ Fin n → α) (s : Finset (Fin n)) (value : α)
    (same : ∀ i ∈ s, ic (.inr i) = value) :
    decode ic (ACUIESolver.Matching.WordRules.atoms (Hom := Hom) s) =
      if s = ∅ then 0 else value := by
  induction s using Finset.induction_on with
  | empty => simp [ACUIESolver.Matching.WordRules.atoms]
  | insert i s _ ih =>
    have head := same i (Finset.mem_insert_self _ _)
    have tail := ih (fun j hj => same j (Finset.mem_insert_of_mem hj))
    simp only [ACUIESolver.Matching.WordRules.atoms, Finset.image_insert, decode,
      ACUIh.NF.eval_insert, ACUIh.Summand.reify, ACUIh.Particle.reify, ACUIh.reifyWord,
      ACUIh.Term.eval, Finset.insert_ne_empty, if_false]
    change ic (.inr i) + decode ic (ACUIESolver.Matching.WordRules.atoms s) = value
    rw [head, tail]
    split_ifs <;> first | exact ACUIh.add_zero _ | exact ACUIh.add_idem _

end ACUIhE.Solver
