import ACUIhE.FILO.Coordinates

/-! Defer column reconstruction while searching E groups. Search and its
completeness argument are unchanged; only materialization of the already
computed FILO reconstruction plans is delayed. -/

namespace ACUIhE.FILO
open ACUIh.Linear
universe u v w k l m
variable {Const : Type u} {Var : Type v} {Hom : Type w}

theorem ColumnCache.collect_map {Key : Type k} {A : Type l} {B : Type m}
    (compute : Key → Option A) (f : A → B) (keys : List Key) :
    collect (fun k => (compute k).map f) keys =
      (collect compute keys).map (fun xs => xs.map (fun x => (x.1, f x.2))) := by
  induction keys with
  | nil => rfl
  | cons key rest ih =>
    cases hk : compute key <;> simp only [collect, hk, Option.map_none, Option.map_some]
    rw [ih]
    cases collect compute rest <;> rfl

variable [DecidableEq Const] [DecidableEq Var] [DecidableEq Hom]

namespace Coordinates

@[noinline] def Prepared.deferColumn (p : Prepared Const Var Hom) (c : Const) :
    Option (Unit → Column Var Hom) :=
  (GenericSolver.search (FlatteningII.normalize (Projection.compile (p.at c) c))).map
    (fun plan _ v => plan.reconstruct (.user v))

theorem Prepared.deferColumn_eq (p : Prepared Const Var Hom) (c : Const) :
    (p.deferColumn c).map (fun f => f ()) = p.solveColumn c := by
  simp only [deferColumn, solveColumn, solveFlatColumn, GenericSolver.solve, Option.map_map]
  rfl

@[noinline] def Prepared.collectDeferred (p : Prepared Const Var Hom) (names : List Const) :
    Option (List (Const × (Unit → Column Var Hom))) := ColumnCache.collect p.deferColumn names

def materialize (s : System Const Var Hom) (cached : List (Const × Column Var Hom)) :
    GroundMatrix Const Var Hom :=
  Column.assemble s.names.toFinset (fun c => (cached.lookup c).getD (fun _ => 0))

def defer (s : System Const Var Hom) : Option (Unit → GroundMatrix Const Var Hom) :=
  ((prepare s).collectDeferred s.names).map
    (fun cached _ => materialize s (cached.map (fun x => (x.1, x.2 ()))))

/-- Exact equality of returned matrices after forcing; no search is repeated. -/
theorem defer_eq (s : System Const Var Hom) :
    (defer s).map (fun f => f ()) = solve s := by
  have collect := ColumnCache.collect_map (prepare s).deferColumn (fun f => f ()) s.names
  simp only [Prepared.deferColumn_eq] at collect
  simp only [defer, Prepared.collectDeferred, solve, Prepared.collect, Option.map_map]
  rw [collect, Option.map_map]
  rfl

theorem defer_sound (s : System Const Var Hom) {f : Unit → GroundMatrix Const Var Hom}
    (found : defer s = some f) : s.IsSolution (f ()) := by
  apply solve_sound s
  rw [← defer_eq, found]
  rfl

theorem defer_none_iff (s : System Const Var Hom) : defer s = none ↔ ¬ s.Unifiable := by
  rw [← solve_none_iff, ← defer_eq, Option.map_eq_none_iff]

end Coordinates
end ACUIhE.FILO
