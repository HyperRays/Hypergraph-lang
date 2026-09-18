import ACUIhE.Solver.Normalization
import ACUIhE.Solver.Prepared

/-!
# Exact separation of canonical layers at E boundaries

Input sides are normalized before separation. E children are named by their
canonical graphs, not by raw terms or forest order. Finite enumerations feed
FILO's term interface; equal child graphs share one defining equation.
-/

namespace ACUIhE.Solver.Preparation

universe u v w x
variable {Const : Type u} {Var : Type v} {Hom : Type w} {α : Type x}

abbrev Variable (Const : Type u) (Var : Type v) (Hom : Type w) := Var ⊕ Graph Const Var Hom
abbrev Forest := Graph.Presentation.Forest
abbrev Tree := Graph.Presentation.Tree

def particle : Graph.Atom Const Var Hom → ACUIh.Particle Const (Variable Const Var Hom)
  | .inl (.const c) => .const c
  | .inl (.var v) => .var (.inl v)
  | .inr child => .var (.inr child.val)

def summand (s : Graph.Summand Const Var Hom) : ACUIh.Summand Const (Variable Const Var Hom) Hom :=
  (s.1, particle s.2)

variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]

/-- An executable enumeration of the canonical ACUIh layer, with E replaced by graph keys. -/
def layer (xs : Forest Const Var Hom) : ACUIh.Term Const (Variable Const Var Hom) Hom :=
  ACUIh.NF.reifyList ((xs.map (fun t => summand t.toSummand)).dedup)

theorem layer_normalize_list (xs : Forest Const Var Hom) :
    (layer xs).normalize = (xs.map (fun t => summand t.toSummand)).toFinset := by
  rw [layer, ACUIh.NF.normalize_reifyList]
  ext s
  simp

/-- Layer semantics is independent of the enumeration used to represent a graph. -/
theorem layer_normalize (xs : Forest Const Var Hom) :
    (layer xs).normalize = (Graph.ofPresentation xs).layer.image summand := by
  rw [layer_normalize_list]
  ext s
  simp [Graph.layer_ofPresentation, Graph.Presentation.toLayer]

def treeBodies (t : Tree Const Var Hom) : List (Forest Const Var Hom) :=
  match t with
  | .atom _ _ => []
  | .edge _ first rest => (first :: rest) ::
      (first :: rest).attach.flatMap (fun t => treeBodies t.val)
termination_by sizeOf t
decreasing_by exact Graph.Presentation.Tree.child_lt _ _ _ (Subtype.property _)

def bodies (xs : Forest Const Var Hom) : List (Forest Const Var Hom) := xs.flatMap treeBodies

omit [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom] in
@[simp] theorem mem_treeBodies_edge (word : List Hom) (first : Tree Const Var Hom)
    (rest : Forest Const Var Hom) (xs : Forest Const Var Hom) :
    xs ∈ treeBodies (.edge word first rest) ↔
      xs = first :: rest ∨ ∃ t ∈ first :: rest, xs ∈ treeBodies t := by
  rw [treeBodies]
  simp only [List.mem_cons, List.mem_flatMap, List.mem_attach, true_and, Subtype.exists,
    exists_prop]

def allBodies (qs : Normalization.Equations Const Var Hom) : List (Forest Const Var Hom) :=
  qs.flatMap (fun q => bodies q.left ++ bodies q.right)

/-- One retained enumeration for each canonical E child in the entire problem. -/
def distinctBodies (qs : Normalization.Equations Const Var Hom) : List (Forest Const Var Hom) :=
  Graph.Enumeration.dedupOn Graph.ofPresentation (allBodies qs)

theorem distinctBodies_nodup (qs : Normalization.Equations Const Var Hom) :
    ((distinctBodies qs).map Graph.ofPresentation).Nodup := by
  rw [distinctBodies, Graph.Enumeration.map_dedupOn]
  exact List.nodup_dedup _

variable [ACUIhE Hom α]
local instance : ACUIh Hom α := reduct

def extend (ic : Const → α) (iv : Var → α) : Variable Const Var Hom → α
  | .inl v => iv v
  | .inr child => E (Hom := Hom) (Graph.eval ic iv child)

theorem layer_eval_congr (ic : Const → α) (iv : Variable Const Var Hom → α)
    {xs ys : Forest Const Var Hom} (same : Graph.ofPresentation xs = Graph.ofPresentation ys) :
    (layer xs).eval ic iv = (layer ys).eval ic iv := by
  apply ACUIh.NF.eval_eq_of_normalize_eq ic iv
  rw [layer_normalize, layer_normalize, same]

@[simp] theorem eval_layer_nil (ic : Const → α) (iv : Variable Const Var Hom → α) :
    (layer ([] : Forest Const Var Hom)).eval ic iv = 0 := rfl

theorem eval_layer_cons (ic : Const → α) (iv : Variable Const Var Hom → α)
    (t : Tree Const Var Hom) (xs : Forest Const Var Hom) :
    (layer (t :: xs)).eval ic iv = (summand t.toSummand).reify.eval ic iv + (layer xs).eval ic iv := by
  rw [← ACUIh.Term.eval_normalize ic iv (layer (t :: xs)), layer_normalize_list,
    List.map_cons, List.toFinset_cons, ACUIh.NF.eval_insert]
  rw [← layer_normalize_list, ACUIh.Term.eval_normalize]

omit [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom] in
private theorem eval_word (ic : Const → α) (iv : Variable Const Var Hom → α) (jv : Var → α)
    (word : List Hom) (a : ACUIh.Term Const (Variable Const Var Hom) Hom)
    (b : Term Const Var Hom) (same : a.eval ic iv = b.eval ic jv) :
    (ACUIh.reifyWord word a).eval ic iv = (Graph.Presentation.applyWord word b).eval ic jv := by
  induction word with
  | nil => exact same
  | cons name word ih => exact congrArg (H name) ih

private theorem eval_layer_of_trees (ic : Const → α) (iv : Variable Const Var Hom → α)
    (jv : Var → α) (xs : Forest Const Var Hom)
    (trees : ∀ t ∈ xs, (summand t.toSummand).reify.eval ic iv = t.reify.eval ic jv) :
    (layer xs).eval ic iv = Graph.eval ic jv (Graph.ofPresentation xs) := by
  induction xs with
  | nil => rfl
  | cons t xs ih =>
    rw [eval_layer_cons, trees t List.mem_cons_self,
      ih (fun s hs => trees s (List.mem_cons_of_mem t hs))]
    rfl

@[simp] theorem eval_layer_extend (ic : Const → α) (iv : Var → α) (xs : Forest Const Var Hom) :
    (layer xs).eval ic (extend ic iv) = Graph.eval ic iv (Graph.ofPresentation xs) := by
  apply eval_layer_of_trees
  intro t _
  cases t with
  | atom word p => cases p <;> exact eval_word ic (extend ic iv) iv word _ _ rfl
  | edge word first rest => exact eval_word ic (extend ic iv) iv word _ _ rfl

private theorem eval_tree (ic : Const → α) (iv : Variable Const Var Hom → α)
    (t : Tree Const Var Hom)
    (edges : ∀ xs ∈ treeBodies t,
      iv (.inr (Graph.ofPresentation xs)) = E (Hom := Hom) ((layer xs).eval ic iv)) :
    (summand t.toSummand).reify.eval ic iv = t.reify.eval ic (fun v => iv (.inl v)) := by
  induction t using (measure (fun t : Tree Const Var Hom => sizeOf t)).wf.induction with
  | h t ih =>
    cases t with
    | atom word p => cases p <;> exact eval_word ic iv (fun v => iv (.inl v)) word _ _ rfl
    | edge word first rest =>
      apply eval_word ic iv (fun v => iv (.inl v)) word
      change iv (.inr (Graph.ofPresentation (first :: rest))) =
        E (Hom := Hom) (Graph.eval ic (fun v => iv (.inl v)) (Graph.ofPresentation (first :: rest)))
      rw [edges (first :: rest) (by simp)]
      apply congrArg E
      apply eval_layer_of_trees
      intro s hs
      apply ih s (Graph.Presentation.Tree.child_lt word first rest hs)
      intro xs hxs
      exact edges xs ((mem_treeBodies_edge _ _ _ _).mpr (.inr ⟨s, hs, hxs⟩))

theorem eval_layer (ic : Const → α) (iv : Variable Const Var Hom → α) (xs : Forest Const Var Hom)
    (edges : ∀ ys ∈ bodies xs,
      iv (.inr (Graph.ofPresentation ys)) = E (Hom := Hom) ((layer ys).eval ic iv)) :
    (layer xs).eval ic iv = Graph.eval ic (fun v => iv (.inl v)) (Graph.ofPresentation xs) := by
  apply eval_layer_of_trees
  intro t ht
  exact eval_tree ic iv t (fun ys hy => edges ys (List.mem_flatMap.mpr ⟨t, ht, hy⟩))

def compileNormalized (qs : Normalization.Equations Const Var Hom) :
    Prepared Const (Variable Const Var Hom) Hom where
  equations := qs.map (fun q => ⟨layer q.left, layer q.right⟩)
  edges := (distinctBodies qs).map (fun xs => ⟨.inr (Graph.ofPresentation xs), layer xs⟩)

def compile (p : Problem Const Var Hom) : Prepared Const (Variable Const Var Hom) Hom :=
  compileNormalized (Normalization.normalize p)

theorem compileNormalized_complete (qs : Normalization.Equations Const Var Hom)
    (ic : Const → α) (iv : Var → α) (h : Normalization.Holds qs ic iv) :
    (compileNormalized qs).Holds ic (extend ic iv) := by
  constructor
  · intro output member
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp member
    change (layer q.left).eval ic (extend ic iv) = (layer q.right).eval ic (extend ic iv)
    simpa only [eval_layer_extend, Normalization.key] using h q hq
  · intro output member
    obtain ⟨xs, _, rfl⟩ := List.mem_map.mp member
    change E (Hom := Hom) (Graph.eval ic iv (Graph.ofPresentation xs)) =
      E (Hom := Hom) ((layer xs).eval ic (extend ic iv))
    rw [eval_layer_extend]

theorem compileNormalized_sound (qs : Normalization.Equations Const Var Hom)
    (ic : Const → α) (iv : Variable Const Var Hom → α) (h : (compileNormalized qs).Holds ic iv) :
    Normalization.Holds qs ic (fun v => iv (.inl v)) := by
  have edge (xs : Forest Const Var Hom) (hx : xs ∈ allBodies qs) :
      iv (.inr (Graph.ofPresentation xs)) = E (Hom := Hom) ((layer xs).eval ic iv) := by
    obtain ⟨ys, hy, same⟩ := Graph.Enumeration.exists_same_key Graph.ofPresentation (allBodies qs) hx
    have valid := h.2 _ (List.mem_map.mpr ⟨ys, hy, rfl⟩)
    change iv (.inr (Graph.ofPresentation ys)) = E (Hom := Hom) ((layer ys).eval ic iv) at valid
    rwa [same, layer_eval_congr ic iv same] at valid
  intro q hq
  have left := eval_layer ic iv q.left (fun xs hx => edge xs
    (List.mem_flatMap.mpr ⟨q, hq, List.mem_append_left _ hx⟩))
  have right := eval_layer ic iv q.right (fun xs hx => edge xs
    (List.mem_flatMap.mpr ⟨q, hq, List.mem_append_right _ hx⟩))
  change Graph.eval ic _ (Graph.ofPresentation q.left) = Graph.eval ic _ (Graph.ofPresentation q.right)
  rw [← left, ← right]
  exact h.1 _ (List.mem_map.mpr ⟨q, hq, rfl⟩)

theorem compile_complete (p : Problem Const Var Hom) (ic : Const → α) (iv : Var → α)
    (h : p.Holds ic iv) : (compile p).Holds ic (extend ic iv) :=
  compileNormalized_complete _ ic iv ((Normalization.holds_normalize_iff p ic iv).mpr h)

theorem compile_sound (p : Problem Const Var Hom) (ic : Const → α)
    (iv : Variable Const Var Hom → α) (h : (compile p).Holds ic iv) :
    p.Holds ic (fun v => iv (.inl v)) :=
  (Normalization.holds_normalize_iff p ic _).mp (compileNormalized_sound _ ic iv h)

end ACUIhE.Solver.Preparation
