import ACUIhE.FILO.Shortcuts.Trace

/-! # From reconstructed particles to the existing generic-system semantics -/

namespace ACUIhE.FILO.Shortcuts

open Components ACUIh.Linear

universe v w

variable {Var : Type v} {Hom : Type w} [DecidableEq Var] [DecidableEq Hom]

def assignment (t : Trace Var Hom) : Column Var Hom :=
  fun v => polynomial t (.var (.base v))

theorem trace_coherent (s : System Var Hom) (root : Node Var Hom) (t : Trace Var Hom)
    (hl : Local s true root) (ht : Realizes s root t) :
    s.Coherent (fun x => polynomial t (.var x)) := by
  intro x hx
  cases x with
  | base v => trivial
  | role r x =>
    apply WordPolynomial.ext
    ext word
    rw [Language.mem_derivative, mem_polynomial, mem_polynomial]
    exact ht.role r x hx word
  | constant x =>
    apply WordPolynomial.ext
    ext word
    rw [Language.mem_constantPart, mem_polynomial, mem_polynomial,
      ht.constant x hx, ht.at_nil]
    have eq := hl.2.2.2.2 (.constant x) hx
    simpa using and_congr_right (fun _ => eq)

theorem trace_atom (s : System Var Hom) (root : Node Var Hom) (t : Trace Var Hom)
    (hl : Local s true root) (ht : Realizes s root t) (a : Atom Var Hom)
    (ha : a ∈ atoms s) : polynomial t a = atomValue (assignment t) a := by
  cases a with
  | const c =>
    cases c
    apply WordPolynomial.ext
    ext word
    change word ∈ (polynomial t (.const ())).words ↔ word ∈ (1 : WordPolynomial Hom).words
    rw [mem_polynomial, ht.literal]
    have present := hl.2.2.2.1.mpr rfl
    simp [present]
  | var x =>
    have hx : x ∈ s.names := by simpa [atoms] using ha
    exact s.coherent_interpret _ (trace_coherent s root t hl ht) hx

/-- No validation step is involved: reconstruction's invariant proves the solution. -/
theorem trace_solution (s : System Var Hom) (root : Node Var Hom) (t : Trace Var Hom)
    (hl : Local s true root) (ht : Realizes s root t) : s.Solution (assignment t) := by
  constructor
  · intro v word hw r hr
    exact List.mem_toFinset.mpr (ht.supported word (.var (.base v))
      ((mem_polynomial _ _ _).mp hw) r hr)
  · intro q hq
    apply (inequality_iff _ _).mpr
    intro word hw
    obtain ⟨a, ha, hw⟩ := (mem_value _ _ _).mp hw
    have inAtoms : ∀ b ∈ q.left ++ q.right, b ∈ atoms s := by
      intro b hb
      cases b with
      | const c => cases c; simp [atoms]
      | var x => simpa [atoms] using s.name_of_mem hq hb
    rw [← trace_atom s root t hl ht a (inAtoms a (List.mem_append_left _ ha)), mem_polynomial] at hw
    obtain ⟨b, hb, hw⟩ := ht.flat word q hq a ha ((mem_slice _ _ _).mpr hw)
    apply (mem_value _ _ _).mpr
    refine ⟨b, hb, ?_⟩
    rw [← trace_atom s root t hl ht b (inAtoms b (List.mem_append_right _ hb)), mem_polynomial]
    exact (mem_slice _ _ _).mp hw

end ACUIhE.FILO.Shortcuts
