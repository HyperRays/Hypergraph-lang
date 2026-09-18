import HMEmbedding.Types

set_option autoImplicit false

/-!
The rank-1 Damas–Milner rules (TAUT, INST, GEN, COMB, ABS, LET), written once
over a type algebra. Source and target operations are defined independently.

Schemes are finite sets of universally bound variable names plus a monotype.
Binder order and repetition have no effect. Instantiation changes only those
names; the freshness condition is precisely that of Damas–Milner §3.
GEN checks the free variables of the entire environment, including captures.

Reference: https://steshaw.org/hm/milner-damas.pdf, §§2–5.
-/

namespace HMEmbedding
open ACUIhE

structure TypeModel where
  Ty : Type
  var : Nat → Ty
  base : Nat → Ty
  op : Op → Ty → Ty → Ty
  equal : Ty → Ty → Prop
  fv : Ty → Finset Nat
  subst : (Nat → Ty) → Ty → Ty

abbrev source : TypeModel where
  Ty := Mono Nat
  var := Mono.var
  base := Mono.base
  op := Mono.op
  equal := Eq
  fv := Mono.fv
  subst := Mono.subst

abbrev target : TypeModel where
  Ty := Fragment
  var v := ⟨.var v, .var v⟩
  base n := ⟨.const (.base n), .base n⟩
  op i a b := ⟨O₂ i a.val b.val, .op i a.property b.property⟩
  equal a b := a.val.Equal b.val
  fv t := freeVars t.val
  subst s t := ⟨t.val.substitute (fun v => (s v).val),
    t.property.substitute _ (fun v => (s v).property)⟩

structure Scheme (M : TypeModel) where
  bound : Finset Nat
  body : M.Ty

def Scheme.mono {M : TypeModel} (t : M.Ty) : Scheme M := ⟨∅, t⟩

def Scheme.all {M : TypeModel} (v : Nat) (s : Scheme M) : Scheme M :=
  ⟨insert v s.bound, s.body⟩

def Scheme.fv {M : TypeModel} (s : Scheme M) : Finset Nat := M.fv s.body \ s.bound

def Scheme.instantiate {M : TypeModel} (s : Scheme M) (args : Nat → M.Ty) : M.Ty :=
  M.subst (fun v => if v ∈ s.bound then args v else M.var v) s.body

/-- The target's equality is ACUIhE equality, not a copied syntactic equality.
Newly quantified names cannot capture any free variable of the original scheme. -/
def Instance {M : TypeModel} (s t : Scheme M) : Prop :=
  ∃ args, M.equal t.body (s.instantiate args) ∧ Disjoint t.bound s.fv

def environmentFV {M : TypeModel} : List (Scheme M) → Finset Nat
  | [] => ∅
  | s :: Γ => s.fv ∪ environmentFV Γ

/-- Term variables use de Bruijn indices; each lambda/let adds one environment entry. -/
inductive Expr where
  | var : Nat → Expr
  | app : Expr → Expr → Expr
  | lam : Expr → Expr
  | letE : Expr → Expr → Expr
  | literal : Nat → Expr
  | pair : Expr → Expr → Expr
  deriving DecidableEq

inductive Typing (M : TypeModel) : List (Scheme M) → Expr → Scheme M → Prop
  | var {Γ n s} : Γ[n]? = some s → Typing M Γ (.var n) s
  | inst {Γ e s t} : Typing M Γ e s → Instance s t → Typing M Γ e t
  | gen {Γ e s v} : Typing M Γ e s → v ∉ environmentFV Γ →
      Typing M Γ e (s.all v)
  | app {Γ f x a b} : Typing M Γ f (.mono (M.op .fn a b)) →
      Typing M Γ x (.mono a) → Typing M Γ (.app f x) (.mono b)
  | lam {Γ e a b} : Typing M (.mono a :: Γ) e (.mono b) →
      Typing M Γ (.lam e) (.mono (M.op .fn a b))
  | letE {Γ value body s t} : Typing M Γ value s →
      Typing M (s :: Γ) body (.mono t) → Typing M Γ (.letE value body) (.mono t)
  | literal {Γ n} : Typing M Γ (.literal n) (.mono (M.base n))
  | pair {Γ a b s t} : Typing M Γ a (.mono s) → Typing M Γ b (.mono t) →
      Typing M Γ (.pair a b) (.mono (M.op .pair s t))

/-- Structure that a type translation must preserve, including semantic equality. -/
structure ModelMap (A B : TypeModel) where
  map : A.Ty → B.Ty
  map_var : ∀ v, map (A.var v) = B.var v
  map_base : ∀ n, map (A.base n) = B.base n
  map_op : ∀ i a b, map (A.op i a b) = B.op i (map a) (map b)
  map_equal : ∀ a b, A.equal a b ↔ B.equal (map a) (map b)
  map_fv : ∀ t, B.fv (map t) = A.fv t
  map_subst : ∀ t s, map (A.subst s t) = B.subst (fun v => map (s v)) (map t)

namespace ModelMap
variable {A B : TypeModel} (f : ModelMap A B)

def scheme (s : Scheme A) : Scheme B := ⟨s.bound, f.map s.body⟩

@[simp] theorem scheme_mono (t : A.Ty) : f.scheme (.mono t) = .mono (f.map t) := rfl

@[simp] theorem scheme_all (s : Scheme A) (v : Nat) :
    f.scheme (s.all v) = (f.scheme s).all v := rfl

@[simp] theorem scheme_fv (s : Scheme A) : (f.scheme s).fv = s.fv := by
  simp only [Scheme.fv, scheme, f.map_fv]

@[simp] theorem environment_fv (Γ : List (Scheme A)) :
    environmentFV (Γ.map f.scheme) = environmentFV Γ := by
  induction Γ <;> simp_all [environmentFV]

theorem scheme_instantiate (s : Scheme A) (args : Nat → A.Ty) :
    f.map (s.instantiate args) = (f.scheme s).instantiate (fun v => f.map (args v)) := by
  unfold Scheme.instantiate
  rw [f.map_subst]
  congr 1
  funext v
  simp only [scheme]
  split <;> simp_all [f.map_var]

theorem instance_map {s t : Scheme A} (h : Instance s t) :
    Instance (f.scheme s) (f.scheme t) := by
  obtain ⟨args, heq, fresh⟩ := h
  refine ⟨fun v => f.map (args v), ?_, ?_⟩
  · have h := (f.map_equal _ _).mp heq
    rw [f.scheme_instantiate] at h
    exact h
  · change Disjoint t.bound (f.scheme s).fv
    rw [f.scheme_fv]
    exact fresh

/-- All HM derivations transfer, including arbitrary nested let and GEN/INST. -/
theorem typing_map {Γ : List (Scheme A)} {e : Expr} {s : Scheme A}
    (h : Typing A Γ e s) : Typing B (Γ.map f.scheme) e (f.scheme s) := by
  induction h with
  | var lookup =>
    apply Typing.var
    simp only [List.getElem?_map, lookup, Option.map_some]
  | inst _ inst ih => exact .inst ih (f.instance_map inst)
  | gen _ fresh ih => exact .gen ih (by simpa only [f.environment_fv] using fresh)
  | app _ _ ih₁ ih₂ =>
    simp only [scheme_mono, f.map_op] at ih₁ ih₂ ⊢
    exact .app ih₁ ih₂
  | lam _ ih =>
    simp only [List.map_cons, scheme_mono, f.map_op] at ih ⊢
    exact .lam ih
  | letE _ _ ih₁ ih₂ =>
    simp only [List.map_cons, scheme_mono] at ih₂ ⊢
    exact .letE ih₁ ih₂
  | literal =>
    simp only [scheme_mono, f.map_base]
    exact .literal
  | pair _ _ ih₁ ih₂ =>
    simp only [scheme_mono, f.map_op] at ih₁ ih₂ ⊢
    exact .pair ih₁ ih₂

end ModelMap

def encoding : ModelMap source target where
  map := embed
  map_var _ := rfl
  map_base _ := rfl
  map_op _ _ _ := rfl
  map_equal a b := (encode_equal_iff a b).symm
  map_fv := encode_fv
  map_subst t s := Subtype.ext (encode_subst t s)

noncomputable def decoding : ModelMap target source where
  map := decode
  map_var v := by change decode (embed (.var v)) = _; exact decode_embed _
  map_base n := by change decode (embed (.base n)) = _; exact decode_embed _
  map_op i a b := by
    apply embed_injective
    rw [embed_decode]
    change target.op i a b = target.op i (embed (decode a)) (embed (decode b))
    rw [embed_decode, embed_decode]
  map_equal a b := by
    have := encoding.map_equal (decode a) (decode b)
    simpa only [encoding, embed_decode] using this.symm
  map_fv t := by
    have := encoding.map_fv (decode t)
    simpa only [encoding, embed_decode] using this.symm
  map_subst t s := by
    apply embed_injective
    rw [embed_decode]
    have := encoding.map_subst (decode t) (fun v => decode (s v))
    simpa only [encoding, embed_decode] using this.symm

@[simp] theorem decode_scheme_encode (s : Scheme source) :
    decoding.scheme (encoding.scheme s) = s := by
  cases s
  simp [ModelMap.scheme, encoding, decoding]

@[simp] theorem encode_scheme_decode (s : Scheme target) :
    encoding.scheme (decoding.scheme s) = s := by
  cases s
  simp [ModelMap.scheme, encoding, decoding]

/-- Full preservation AND reflection of rank-1 HM typing in the O_i fragment. -/
theorem full_hm_embedding (Γ : List (Scheme source)) (e : Expr) (s : Scheme source) :
    Typing source Γ e s ↔ Typing target (Γ.map encoding.scheme) e (encoding.scheme s) := by
  constructor
  · exact encoding.typing_map
  · intro h
    have := decoding.typing_map h
    simpa [List.map_map, Function.comp_def] using this

theorem instance_iff (s t : Scheme source) :
    Instance s t ↔ Instance (encoding.scheme s) (encoding.scheme t) := by
  constructor
  · exact encoding.instance_map
  · intro h
    simpa only [decode_scheme_encode] using decoding.instance_map h

/-- Principality is a property, not an MGU algorithm: every other assignable
scheme is an instance of this one. -/
def Principal (M : TypeModel) (Γ : List (Scheme M)) (e : Expr) (s : Scheme M) : Prop :=
  Typing M Γ e s ∧ ∀ t, Typing M Γ e t → Instance s t

theorem principal_iff (Γ : List (Scheme source)) (e : Expr) (s : Scheme source) :
    Principal source Γ e s ↔
      Principal target (Γ.map encoding.scheme) e (encoding.scheme s) := by
  constructor
  · rintro ⟨typed, principal⟩
    refine ⟨encoding.typing_map typed, ?_⟩
    intro t ht
    have h := decoding.typing_map ht
    simp [List.map_map, Function.comp_def] at h
    have specialized := encoding.instance_map (principal _ h)
    simpa only [encode_scheme_decode] using specialized
  · rintro ⟨typed, principal⟩
    refine ⟨(full_hm_embedding Γ e s).mpr typed, ?_⟩
    intro t ht
    exact (instance_iff s t).mpr (principal _ (encoding.typing_map ht))

end HMEmbedding
