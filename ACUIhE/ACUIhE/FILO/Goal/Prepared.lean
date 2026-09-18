import ACUIhE.FILO.Goal.Implicit
import ACUIhE.FILO.Shortcuts.Completeness

/-! # Choice-specific goals, starts, and shortcut admissibility -/

namespace ACUIhE.FILO.Goal

open Components ACUIh.Linear Choices Shortcuts

universe v w

structure Prepared (Var : Type v) (Hom : Type w) where
  source : System Var Hom
  choice : Choice Var Hom
  unsolved : List (Requirement Var Hom)

variable {Var : Type v} {Hom : Type w} [DecidableEq Var] [DecidableEq Hom]

namespace Prepared

def Valid (g : Prepared Var Hom) : Prop :=
  Consistent g.source g.choice ∧ Implicit.reduce g.source g.choice = some g.unsolved

def root (g : Prepared Var Hom) : Node Var Hom :=
  insert (.const ()) ((g.source.names.filter (fun x => g.choice x == .constant)).map (.var ·)).toFinset

@[simp] theorem mem_root_var (g : Prepared Var Hom) (x : Variable Var Hom) :
    .var x ∈ g.root ↔ x ∈ g.source.names ∧ g.choice x = .constant := by simp [root]

def Compatible (g : Prepared Var Hom) (initial : Bool) (node : Node Var Hom) : Prop :=
  node ⊆ (atoms g.source).toFinset ∧
  (.const () ∈ node ↔ initial = true) ∧
  (∀ x ∈ g.source.names, g.choice x = .top → .var x ∉ node) ∧
  (∀ x ∈ g.source.names, initial = true → (.var x ∈ node ↔ g.choice x = .constant)) ∧
  (∀ x, .constant x ∈ g.source.names → initial = false → .var (.constant x) ∉ node)

def Flat (g : Prepared Var Hom) (node : Node Var Hom) : Prop :=
  ∀ q ∈ g.unsolved, q.Present (· ∈ node)

instance (g : Prepared Var Hom) (node : Node Var Hom) : Decidable (g.Flat node) :=
  inferInstanceAs (Decidable (∀ q ∈ g.unsolved,
    q.required ∈ node → ∃ a ∈ q.available, a ∈ node))

theorem compatible_fits (g : Prepared Var Hom) (initial : Bool) (node : Node Var Hom)
    (h : g.Compatible initial node) {q : Requirement Var Hom} (hq : q ∈ requirements g.source.flat) :
    Implicit.Fits g.choice initial (· ∈ node) q := by
  intro a ha
  cases a with
  | const label =>
    cases label
    refine ⟨by simp [atomStatus], ?_, fun _ => h.2.1⟩
    intro hi
    simp only [atomStatus, iff_true]
    exact h.2.1.mpr hi
  | var x =>
    have hx := requirement_names g.source hq (List.mem_cons.mp ha)
    exact ⟨h.2.2.1 x hx, h.2.2.2.1 x hx, by simp⟩

theorem compatible_local (g : Prepared Var Hom) (valid : g.Valid) (initial : Bool)
    (node : Node Var Hom) (compatible : g.Compatible initial node) (flat : g.Flat node) :
    Shortcuts.Local g.source initial node := by
  refine ⟨compatible.1, ?_, ?_, compatible.2.1, ?_⟩
  · have original := (Implicit.reduce_some_correct g.source g.choice valid.2 initial
      (· ∈ node) (fun _ hq => g.compatible_fits initial node compatible hq)).mpr flat
    intro q hq a ha hm
    exact original ⟨a, q.right⟩ (List.mem_flatMap.mpr
      ⟨q, hq, List.mem_map.mpr ⟨a, ha, rfl⟩⟩) hm
  · intro x hx
    cases x with
    | base v | constant p => trivial
    | role r p =>
      intro hm
      by_contra absent
      exact compatible.2.2.1 (.role r p) hx ((valid.1 _ hx).2.1 absent) hm
  · intro x hx
    cases x with
    | base v | role r p => trivial
    | constant p =>
      cases initial with
      | false => simpa using compatible.2.2.2.2 p hx rfl
      | true =>
        simp only [true_and]
        rw [compatible.2.2.2.1 (.constant p) hx rfl,
          compatible.2.2.2.1 p (g.source.parent_constant hx) rfl]
        exact (valid.1 _ hx).2

theorem root_compatible (g : Prepared Var Hom) : g.Compatible true g.root := by
  refine ⟨?_, by simp [root], ?_, ?_, by simp⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · simp [atoms]
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
      simp only [List.mem_filter] at hx
      simpa [atoms] using hx.1
  · intro x hx top
    simp [top]
  · intro x hx _
    simp [hx]

def active (g : Prepared Var Hom) : List (Atom Var Hom) :=
  (g.source.names.filter (fun x => decide (g.choice x ≠ .top) &&
    match x with | .constant _ => false | _ => true)).map (.var ·)

@[simp] theorem mem_active_var (g : Prepared Var Hom) (x : Variable Var Hom) :
    .var x ∈ g.active ↔ x ∈ g.source.names ∧ g.choice x ≠ .top ∧
      (match x with | .constant _ => False | _ => True) := by
  cases x <;> simp [active]

@[simp] theorem literal_not_active (g : Prepared Var Hom) : .const () ∉ g.active := by simp [active]

theorem subset_active_compatible (g : Prepared Var Hom) (node : Node Var Hom)
    (sub : node ⊆ g.active.toFinset) : g.Compatible false node := by
  have member : ∀ a ∈ node, a ∈ g.active := fun a ha => List.mem_toFinset.mp (sub ha)
  refine ⟨?_, ?_, ?_, by simp, ?_⟩
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (member a ha)
    exact List.mem_toFinset.mpr (by simpa [atoms] using (List.mem_filter.mp hx).1)
  · simp only [Bool.false_eq_true, iff_false]
    exact fun h => g.literal_not_active (member _ h)
  · intro x _ ht hx
    exact ((mem_active_var g x).mp (member _ hx)).2.1 ht
  · intro x _ _ hx
    have impossible := (mem_active_var g (.constant x)).mp (member _ hx) |>.2.2
    exact impossible

theorem compatible_subset_active (g : Prepared Var Hom) (node : Node Var Hom)
    (h : g.Compatible false node) : node ⊆ g.active.toFinset := by
  intro a ha
  have names := List.mem_toFinset.mp (h.1 ha)
  cases a with
  | const label => cases label; exact False.elim (Bool.false_ne_true (h.2.1.mp ha))
  | var x =>
    have hx : x ∈ g.source.names := by simpa [atoms] using names
    apply List.mem_toFinset.mpr
    apply (mem_active_var g x).mpr
    refine ⟨hx, fun top => h.2.2.1 x hx top ha, ?_⟩
    cases x with
    | base v | role r p => trivial
    | constant p => exact h.2.2.2.2 p hx rfl ha

def Normal (g : Prepared Var Hom) (node : Node Var Hom) : Prop :=
  node ⊆ g.active.toFinset ∧ g.Flat node

instance (g : Prepared Var Hom) (node : Node Var Hom) : Decidable (g.Normal node) :=
  inferInstanceAs (Decidable (node ⊆ g.active.toFinset ∧ g.Flat node))

theorem normal_local (g : Prepared Var Hom) (valid : g.Valid) (node : Node Var Hom)
    (h : g.Normal node) : Shortcuts.Local g.source false node :=
  g.compatible_local valid false node (g.subset_active_compatible node h.1) h.2

theorem atWord_compatible (g : Prepared Var Hom) (iv : Column Var Hom)
    (hc : Classifies g.source g.choice iv) (word : List Hom) :
    g.Compatible (decide (word = [])) (atWord g.source iv word) := by
  refine ⟨Finset.filter_subset _ _, ?_, ?_, ?_, ?_⟩
  · simp [mem_atWord, atoms, atomValue]
  · intro x hx top member
    have hm := (mem_atWord _ _ _ _).mp member |>.2
    have zero := (classify_top _).mp ((hc x hx) ▸ top)
    change word ∈ (interpret iv x).words at hm
    rw [zero] at hm
    exact Finset.notMem_empty _ hm
  · intro x hx initial
    have eq := of_decide_eq_true initial
    simp [eq, mem_atWord, var_in_atoms, hx, atomValue, hc x hx]
  · intro x hx initial member
    have notNil : word ≠ [] := of_decide_eq_false initial
    have hm := (mem_atWord _ _ _ _).mp member |>.2
    exact notNil ((Language.mem_constantPart _ _).mp hm |>.1)

theorem atWord_flat (g : Prepared Var Hom) (valid : g.Valid) (iv : Column Var Hom)
    (solution : g.source.Solution iv) (hc : Classifies g.source g.choice iv) (word : List Hom) :
    g.Flat (atWord g.source iv word) := by
  apply (Implicit.reduce_some_correct _ _ valid.2 (decide (word = []))
    (· ∈ atWord g.source iv word) (fun _ hq =>
      g.compatible_fits _ _ (g.atWord_compatible iv hc word) hq)).mp
  intro q hq hm
  obtain ⟨e, he, hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
  exact (atWord_local g.source iv solution word).2.1 e he a ha hm

theorem atWord_root (g : Prepared Var Hom) (iv : Column Var Hom)
    (hc : Classifies g.source g.choice iv) : atWord g.source iv [] = g.root := by
  ext a
  cases a with
  | const label => cases label; simp [root, mem_atWord, atoms, atomValue]
  | var x =>
    by_cases hx : x ∈ g.source.names
    · simp [mem_atWord, var_in_atoms, mem_root_var, hx, hc x hx, atomValue]
    · simp [mem_atWord, var_in_atoms, mem_root_var, hx]

end Prepared

end ACUIhE.FILO.Goal
