type term =
  | Zero
  | Constant of string
  | Variable of string
  | Sum of term list
  | Hom of string * term
  | E of term

type constraint_ = Equal of term * term | Below of term * term
type replacement = { pattern : term; replacement : term }
type assignment = (string * term) list
type solution = Sat of assignment | Unsat
type error = Lean_bridge.error

let empty = Zero
let constant name = Constant name
let variable name = Variable name

let sum terms =
  let rec flatten acc = function
    | [] -> List.rev acc
    | Zero :: rest -> flatten acc rest
    | Sum nested :: rest -> flatten acc (nested @ rest)
    | term :: rest -> flatten (term :: acc) rest
  in
  match flatten [] terms with [] -> Zero | [ term ] -> term | terms -> Sum terms

let hom name body = Hom (name, body)
let e body = E body
let replacement ~pattern ~replacement = { pattern; replacement }
let of_subsumption ~lower ~upper = { pattern = upper; replacement = sum [ upper; lower ] }

module String_set = Set.Make (String)

type names = {
  constants : String_set.t;
  variables : String_set.t;
  homomorphisms : String_set.t;
}

let no_names =
  { constants = String_set.empty; variables = String_set.empty;
    homomorphisms = String_set.empty }

let rec collect_term names = function
  | Zero -> names
  | Constant name -> { names with constants = String_set.add name names.constants }
  | Variable name -> { names with variables = String_set.add name names.variables }
  | Sum terms -> List.fold_left collect_term names terms
  | Hom (name, body) ->
      collect_term
        { names with homomorphisms = String_set.add name names.homomorphisms }
        body
  | E body -> collect_term names body

let collect_constraint names = function
  | Equal (left, right) | Below (left, right) ->
      collect_term (collect_term names left) right

let collect_replacement names rule =
  collect_term (collect_term names rule.pattern) rule.replacement

let has_variable term =
  let rec loop = function
    | Variable _ -> true
    | Sum terms -> List.exists loop terms
    | Hom (_, body) | E body -> loop body
    | Zero | Constant _ -> false
  in
  loop term

type table = { count : int; index : string -> int; ordered : string list }

let table set =
  let ordered = String_set.elements set in
  let entries = Hashtbl.create (List.length ordered) in
  List.iteri (fun index name -> Hashtbl.add entries name index) ordered;
  { count = List.length ordered; index = Hashtbl.find entries; ordered }

let rec json_of_term constants variables homomorphisms = function
  | Zero -> `Assoc [ ("tag", `String "zero") ]
  | Constant name ->
      `Assoc [ ("tag", `String "const"); ("id", `Int (constants.index name)) ]
  | Variable name ->
      `Assoc [ ("tag", `String "var"); ("id", `Int (variables.index name)) ]
  | Sum [] -> `Assoc [ ("tag", `String "zero") ]
  | Sum (first :: rest) ->
      List.fold_left
        (fun left right ->
          `Assoc
            [ ("tag", `String "add"); ("left", left);
              ("right", json_of_term constants variables homomorphisms right) ])
        (json_of_term constants variables homomorphisms first)
        rest
  | Hom (name, body) ->
      `Assoc
        [ ("tag", `String "hom"); ("id", `Int (homomorphisms.index name));
          ("body", json_of_term constants variables homomorphisms body) ]
  | E body ->
      `Assoc
        [ ("tag", `String "free");
          ("body", json_of_term constants variables homomorphisms body) ]

let rec term_of_json constants homomorphisms = function
  | `Assoc fields -> (
      let field name = List.assoc_opt name fields in
      match field "tag" with
      | Some (`String "zero") -> Ok Zero
      | Some (`String "const") -> (
          match field "id" with
          | Some (`Int id) -> (
              match List.nth_opt constants id with
              | Some name -> Ok (Constant name)
              | None -> Error { Lean_bridge.message = "invalid constant in solver response" })
          | _ -> Error { Lean_bridge.message = "missing constant id in solver response" })
      | Some (`String "hom") -> (
          match (field "id", field "body") with
          | Some (`Int id), Some body -> (
              match List.nth_opt homomorphisms id with
              | None -> Error { Lean_bridge.message = "invalid homomorphism in solver response" }
              | Some name ->
                  Result.map (fun body -> Hom (name, body))
                    (term_of_json constants homomorphisms body))
          | _ -> Error { Lean_bridge.message = "malformed homomorphism in solver response" })
      | Some (`String "free") -> (
          match field "body" with
          | Some body -> Result.map (fun body -> E body)
              (term_of_json constants homomorphisms body)
          | None -> Error { Lean_bridge.message = "missing E body in solver response" })
      | Some (`String "add") -> (
          match (field "left", field "right") with
          | Some left, Some right ->
              Result.bind (term_of_json constants homomorphisms left) (fun left ->
                Result.map (fun right -> sum [ left; right ])
                  (term_of_json constants homomorphisms right))
          | _ -> Error { Lean_bridge.message = "malformed sum in solver response" })
      | _ -> Error { Lean_bridge.message = "unknown term in solver response" })
  | _ -> Error { Lean_bridge.message = "non-object term in solver response" }

let solve ?(rules = []) constraints =
  match
    List.find_opt
      (fun rule -> has_variable rule.pattern || has_variable rule.replacement)
      rules
  with
  | Some _ ->
      Error { Lean_bridge.message = "external replacement rules must be ground" }
  | None ->
      let names =
        List.fold_left collect_constraint
          (List.fold_left collect_replacement no_names rules)
          constraints
      in
      let constants = table names.constants
      and variables = table names.variables
      and homomorphisms = table names.homomorphisms in
      let encode = json_of_term constants variables homomorphisms in
      let rules_json =
        `List
          (List.map
             (fun rule ->
               `Assoc
                 [ ("pattern", encode rule.pattern);
                   ("replacement", encode rule.replacement) ])
             rules)
      in
      let constraints_json =
        `List
          (List.map
             (function
               | Equal (left, right) ->
                   `Assoc
                     [ ("kind", `String "equal"); ("left", encode left);
                       ("right", encode right) ]
               | Below (left, right) ->
                   `Assoc
                     [ ("kind", `String "below"); ("left", encode left);
                       ("right", encode right) ])
             constraints)
      in
      let request =
        `Assoc
          [ ("version", `Int 1); ("operation", `String "solve");
            ("constants", `Int constants.count);
            ("variables", `Int variables.count);
            ("homomorphisms", `Int homomorphisms.count);
            ("rules", rules_json); ("constraints", constraints_json) ]
      in
      Result.bind (Lean_bridge.invoke request) (function
        | `Assoc fields -> (
            match List.assoc_opt "status" fields with
            | Some (`String "unsat") -> Ok Unsat
            | Some (`String "sat") -> (
                match List.assoc_opt "assignment" fields with
                | Some (`List values)
                  when List.length values = variables.count ->
                    let rec decode names values acc =
                      match (names, values) with
                      | [], [] -> Ok (Sat (List.rev acc))
                      | name :: names, value :: values ->
                          Result.bind
                            (term_of_json constants.ordered homomorphisms.ordered value)
                            (fun term -> decode names values ((name, term) :: acc))
                      | _ ->
                          Error { Lean_bridge.message = "solver assignment length mismatch" }
                    in
                    decode variables.ordered values []
                | _ -> Error { Lean_bridge.message = "missing solver assignment" })
            | _ -> Error { Lean_bridge.message = "unknown solver status" })
        | _ -> Error { Lean_bridge.message = "non-object solver response" })

let rec substitute assignment = function
  | Zero -> Zero
  | Constant _ as term -> term
  | Variable name -> Option.value (List.assoc_opt name assignment) ~default:(Variable name)
  | Sum terms -> sum (List.map (substitute assignment) terms)
  | Hom (name, body) -> Hom (name, substitute assignment body)
  | E body -> E (substitute assignment body)

let check_assignment ?(rules = []) constraints assignment =
  let grounded =
    List.map
      (function
        | Equal (left, right) ->
            Equal (substitute assignment left, substitute assignment right)
        | Below (left, right) ->
            Below (substitute assignment left, substitute assignment right))
      constraints
  in
  if List.exists
       (function
         | Equal (left, right) | Below (left, right) ->
             has_variable left || has_variable right)
       grounded
  then Error { Lean_bridge.message = "assignment does not bind every constraint variable" }
  else Result.map (function Sat _ -> true | Unsat -> false) (solve ~rules grounded)

let rec pp_term formatter = function
  | Zero -> Format.pp_print_string formatter "0"
  | Constant name -> Format.pp_print_string formatter name
  | Variable name -> Format.fprintf formatter "?%s" name
  | Sum terms ->
      Format.pp_print_list
        ~pp_sep:(fun formatter () -> Format.pp_print_string formatter " + ")
        pp_term formatter terms
  | Hom (name, body) -> Format.fprintf formatter "%s(%a)" name pp_term body
  | E body -> Format.fprintf formatter "E(%a)" pp_term body
