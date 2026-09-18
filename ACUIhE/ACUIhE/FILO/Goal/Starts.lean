import ACUIhE.FILO.Goal.Prepared
import ACUIhE.FILO.Shortcuts.Semantics

/-! # Rule 9: direct reconstruction from starts and increasing subsumptions

When the implicit solver leaves no flat requirements, propagate the start
particles to their parents. Structural component depth bounds this recursion;
no shortcut subsets or saturation layers are generated on this path.
-/

namespace ACUIhE.FILO.Goal.Starts

open Components ACUIh.Linear Choices Shortcuts

universe v w

variable {Var : Type v} {Hom : Type w} [DecidableEq Var] [DecidableEq Hom]

def parents (g : Prepared Var Hom) (r : Hom) (node : Node Var Hom) : Node Var Hom :=
  (g.source.names.filterMap (fun x => match x with
    | .role t p => if t = r ∧ .var x ∈ node then some (.var p) else none
    | _ => none)).toFinset

theorem mem_parents (g : Prepared Var Hom) (r : Hom) (node : Node Var Hom) (a : Atom Var Hom) :
    a ∈ parents g r node ↔ ∃ p, .role r p ∈ g.source.names ∧ .var (.role r p) ∈ node ∧ a = .var p := by
  simp only [parents, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, h⟩
    cases x with
    | base v | constant p => cases h
    | role t p =>
      change (if t = r ∧ .var (.role t p) ∈ node then some (.var p) else none) = some a at h
      by_cases condition : t = r ∧ .var (.role t p) ∈ node
      · rw [if_pos condition] at h
        obtain ⟨eq, member⟩ := condition
        subst t
        exact ⟨p, hx, member, (Option.some.inj h).symm⟩
      · rw [if_neg condition] at h
        cases h
  · rintro ⟨p, hp, member, rfl⟩
    exact ⟨.role r p, hp, by simp [member]⟩

theorem parents_resolve (g : Prepared Var Hom) (r : Hom) (node : Node Var Hom) :
    Resolves g.source node r (parents g r node) := by
  intro x hx
  cases x with
  | base v | constant p => trivial
  | role t p =>
    intro eq; subst t
    rw [mem_parents]
    constructor
    · intro hm; exact ⟨p, hx, hm, rfl⟩
    · rintro ⟨q, _, hm, eq⟩
      have eq' : p = q := ACUIh.Particle.var.inj eq
      exact eq' ▸ hm

theorem parents_empty (g : Prepared Var Hom) (r : Hom) (node : Node Var Hom)
    (h : ¬ Needs g.source node r) : parents g r node = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨p, hp, hm, _⟩ := (mem_parents _ _ _ _).mp ha
  exact h (needs_of_member g.source hp hm)

theorem parents_compatible (g : Prepared Var Hom) (valid : g.Valid) (initial : Bool)
    (node : Node Var Hom) (compatible : g.Compatible initial node) (r : Hom) :
    g.Compatible false (parents g r node) := by
  refine ⟨?_, ?_, ?_, by simp, ?_⟩
  · intro a ha
    obtain ⟨p, hp, _, rfl⟩ := (mem_parents _ _ _ _).mp ha
    exact List.mem_toFinset.mpr (by simpa [atoms] using g.source.parent_role hp)
  · simp only [Bool.false_eq_true, iff_false]
    intro ha
    obtain ⟨p, _, _, impossible⟩ := (mem_parents _ _ _ _).mp ha
    cases impossible
  · intro p hp top ha
    obtain ⟨q, hq, hm, eq⟩ := (mem_parents _ _ _ _).mp ha
    have same : p = q := ACUIh.Particle.var.inj eq
    subst q
    exact compatible.2.2.1 (.role r p) hq ((valid.1 _ hq).1 top) hm
  · intro p hp _ ha
    obtain ⟨q, hq, hm, eq⟩ := (mem_parents _ _ _ _).mp ha
    have same : .constant p = q := ACUIh.Particle.var.inj eq
    subst q
    exact compatible.2.2.1 (.role r (.constant p)) hq ((valid.1 _ hq).2.2) hm

def depth : Variable Var Hom → Nat
  | .base _ => 0
  | .role _ p | .constant p => depth p + 1

def Bounded (n : Nat) (node : Node Var Hom) : Prop :=
  ∀ x, .var x ∈ node → depth x ≤ n

theorem parents_bounded (g : Prepared Var Hom) (r : Hom) (node : Node Var Hom) (n : Nat)
    (h : Bounded (n + 1) node) : Bounded n (parents g r node) := by
  intro x hx
  obtain ⟨p, hp, member, eq⟩ := (mem_parents _ _ _ _).mp hx
  have same : x = p := ACUIh.Particle.var.inj eq
  subst p
  have bound := h (.role r x) member
  simp only [depth] at bound
  omega

theorem zero_not_needed (g : Prepared Var Hom) (node : Node Var Hom)
    (h : Bounded 0 node) (r : Hom) : ¬ Needs g.source node r := by
  rintro ⟨x, hx, active⟩
  cases x with
  | base v | constant p => exact active
  | role t p =>
    have bound := h (.role t p) active.2
    simp [depth] at bound

def build (g : Prepared Var Hom) : Nat → Node Var Hom → Trace Var Hom
  | 0, node => graft g.source.roles node (fun _ => ∅)
  | n + 1, node => graft g.source.roles node (fun r =>
      if Needs g.source node r then build g n (parents g r node) else ∅)

theorem build_correct (g : Prepared Var Hom) (valid : g.Valid) (empty : g.unsolved = [])
    (n : Nat) (node : Node Var Hom) (initial : Bool)
    (compatible : g.Compatible initial node) (bound : Bounded n node) :
    Realizes g.source node (build g n node) := by
  have noFlat : ∀ t, g.Flat t := by intro t; simp [Prepared.Flat, empty]
  have localRoot := g.compatible_local valid initial node compatible (noFlat node)
  induction n generalizing node initial with
  | zero =>
    apply realizes_graft g.source initial node localRoot (fun _ => ∅) (fun _ => ∅)
    · intro r hr; exact local_empty g.source
    · intro r hr; exact realizes_empty g.source
    · intro r hr
      have eq := parents_empty g r node (zero_not_needed g node bound r)
      simpa [eq] using parents_resolve g r node
  | succ n ih =>
    apply realizes_graft g.source initial node localRoot (fun r => parents g r node)
    · intro r hr
      exact g.compatible_local valid false _ (parents_compatible g valid initial node compatible r) (noFlat _)
    · intro r hr
      by_cases needed : Needs g.source node r
      · simp only [if_pos needed]
        exact ih _ false (parents_compatible g valid initial node compatible r)
          (parents_bounded g r node n bound)
          (g.compatible_local valid false _ (parents_compatible g valid initial node compatible r) (noFlat _))
      · simpa [needed, parents_empty g r node needed] using realizes_empty g.source
    · intro r hr; exact parents_resolve g r node

def height (g : Prepared Var Hom) : Nat := g.source.names.toFinset.sup depth

theorem root_bounded (g : Prepared Var Hom) : Bounded (height g) g.root := by
  intro x hx
  have member := (Prepared.mem_root_var g x).mp hx |>.1
  exact Finset.le_sup (f := depth) (List.mem_toFinset.mpr member)

def solve (g : Prepared Var Hom) : Column Var Hom := assignment (build g (height g) g.root)

theorem solve_sound (g : Prepared Var Hom) (valid : g.Valid) (empty : g.unsolved = []) :
    g.source.Solution (solve g) := by
  have flat : g.Flat g.root := by simp [Prepared.Flat, empty]
  exact trace_solution g.source g.root _
    (g.compatible_local valid true g.root g.root_compatible flat)
    (build_correct g valid empty (height g) g.root true g.root_compatible (root_bounded g))

end ACUIhE.FILO.Goal.Starts
