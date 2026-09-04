open Hypergraph

type error = { message : string }

val schema : Check.checked -> (string, error) result
val facts : ?tag:string -> Program.result -> (string, error) result
