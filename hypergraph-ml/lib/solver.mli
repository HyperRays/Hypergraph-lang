type term
type constraint_ = Equal of term * term | Below of term * term
type replacement
type assignment = (string * term) list
type solution = Sat of assignment | Unsat
type error = Lean_bridge.error

val bottom : term
val constant : string -> term
val variable : string -> term
val sum : term list -> term
val hom : string -> term -> term
val e : term -> term

val replacement : pattern:term -> replacement:term -> replacement
val of_subsumption : lower:term -> upper:term -> replacement

val solve : ?rules:replacement list -> constraint_ list ->
  (solution, error) result

val check_assignment : ?rules:replacement list -> constraint_ list ->
  assignment -> (bool, error) result

val substitute : assignment -> term -> term
val pp_term : Format.formatter -> term -> unit
