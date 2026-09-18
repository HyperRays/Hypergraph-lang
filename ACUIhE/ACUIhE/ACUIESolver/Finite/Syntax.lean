import ACUIhE.ACUIESolver.Finite.Algebra

/-! # The finite, subterm-closed input signature -/

deriving instance DecidableEq for ACUIhE.ACUIE.Term

namespace ACUIhE.ACUIESolver.Finite

universe u v
variable {Const : Type u} {Var : Type v}

def subterms (t : ACUIE.Term Const Var) : List (ACUIE.Term Const Var) :=
  t :: match t with
    | .zero | .const _ | .var _ => []
    | .add a b => subterms a ++ subterms b
    | .free a => subterms a

theorem mem_subterms_self (t : ACUIE.Term Const Var) : t ∈ subterms t := by
  cases t <;> simp [subterms]

theorem subterms_closed {s t : ACUIE.Term Const Var} (h : s ∈ subterms t) :
    subterms s ⊆ subterms t := by
  induction t with
  | zero | const | var =>
    simp only [subterms, List.mem_cons, List.not_mem_nil, or_false] at h
    subst s
    exact List.Subset.refl _
  | add a b ha hb =>
    rw [subterms, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · exact List.Subset.refl _
    · intro x hx
      simp only [subterms, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inl (ha h hx))
    · intro x hx
      simp only [subterms, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inr (hb h hx))
  | free a ha =>
    rw [subterms, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.Subset.refl _
    · intro x hx
      rw [subterms, List.mem_cons]
      exact Or.inr (ha h hx)

def pool (p : Problem Const Var) : List (ACUIE.Term Const Var) :=
  p.flatMap (fun q => subterms q.left ++ subterms q.right)

def Closed (ts : List (ACUIE.Term Const Var)) : Prop := ∀ t ∈ ts, subterms t ⊆ ts

theorem pool_closed (p : Problem Const Var) : Closed (pool p) := by
  intro t ht s hs
  obtain ⟨q, hq, ht⟩ := List.mem_flatMap.mp ht
  apply List.mem_flatMap.mpr
  refine ⟨q, hq, ?_⟩
  rcases List.mem_append.mp ht with ht | ht
  · exact List.mem_append_left _ (subterms_closed ht hs)
  · exact List.mem_append_right _ (subterms_closed ht hs)

theorem pool_left (p : Problem Const Var) {q : ACUIE.Equation Const Var} (h : q ∈ p) :
    q.left ∈ pool p := List.mem_flatMap.mpr
  ⟨q, h, List.mem_append_left _ (mem_subterms_self _)⟩

theorem pool_right (p : Problem Const Var) {q : ACUIE.Equation Const Var} (h : q ∈ p) :
    q.right ∈ pool p := List.mem_flatMap.mpr
  ⟨q, h, List.mem_append_right _ (mem_subterms_self _)⟩

theorem Closed.add_left {ts : List (ACUIE.Term Const Var)} (h : Closed ts)
    {a b : ACUIE.Term Const Var} (member : .add a b ∈ ts) : a ∈ ts :=
  h _ member (List.mem_cons_of_mem _ (List.mem_append_left _ (mem_subterms_self _)))

theorem Closed.add_right {ts : List (ACUIE.Term Const Var)} (h : Closed ts)
    {a b : ACUIE.Term Const Var} (member : .add a b ∈ ts) : b ∈ ts :=
  h _ member (List.mem_cons_of_mem _ (List.mem_append_right _ (mem_subterms_self _)))

theorem Closed.free_body {ts : List (ACUIE.Term Const Var)} (h : Closed ts)
    {a : ACUIE.Term Const Var} (member : .free a ∈ ts) : a ∈ ts :=
  h _ member (List.mem_cons_of_mem _ (mem_subterms_self _))

end ACUIhE.ACUIESolver.Finite
