(** Native bindings to the verified Lean ACUIhE solver. Values are opaque
    reference-counted Lean objects, released by OCaml finalizers. They may be
    shared across threads/domains, but cannot be marshalled. Symbol IDs must be
    nonnegative OCaml ints; constants, variables, and homomorphisms have separate
    namespaces. Use the equality functions below instead of polymorphic [(=)]. *)

module Term : sig
  type t
  val zero : t
  val constant : int -> t
  val variable : int -> t
  val add : t -> t -> t
  val hom : int -> t -> t
  val free : t -> t
  val equal : t -> t -> bool
  val below : t -> t -> bool
end

module Graph : sig
  type t
  type atom = Constant of int | Variable of int | Free of t
  type summand = { word : int array; atom : atom }

  val normalize : Term.t -> t
  val equal : t -> t -> bool
  val below : t -> t -> bool

  (** One unordered, duplicate-free layer. Words are outermost-first;
      [Free child] represents an E edge to a nonempty child graph. *)
  val layer : t -> summand array

  (** Reconstruct a raw term using the public layer view. Enumeration order is
      unspecified. The result is algebraically equal to the graph, and may be
      larger than the shared native representation. *)
  val to_term : t -> Term.t
end

module Solution : sig
  type t

  (** Query one ground assignment. IDs absent from the problem map to zero. *)
  val get : t -> int -> Graph.t
end

type equation = Term.t * Term.t

(** [None] means unsatisfiable. [Some solution] is one ground substitution,
    without a guarantee of minimality or most-generality. Calls release the
    OCaml runtime lock while Lean searches. *)
val solve : equation array -> Solution.t option

(** Decide satisfiability without reconstructing a substitution. *)
val is_unifiable : equation array -> bool

type constraint_ = Equal of Term.t * Term.t | Below of Term.t * Term.t

(** Inclusion [a <= b] is translated to the equation [a + b = b]. *)
val solve_constraints : constraint_ array -> Solution.t option
val constraints_satisfiable : constraint_ array -> bool
