module String_map = Map.Make (String)

type diagnostic = { loc : Ast.loc; message : string }

type declaration_kind = Struct_kind | Enum_kind

type declaration = {
  kind : declaration_kind;
  name : string;
  parameters : string list;
  members : (string * Ast.ty) list;
  (* Resolved once by the checker so downstream consumers never need to
     duplicate alias or generic-type interpretation. *)
  resolved_members : (string * Types.t) list;
}

type binding = {
  name : string;
  mutable_ : bool;
  ty : Types.t;
  solved_type : Solver.term;
  marker : Types.t;
  loc : Ast.loc;
}

type checked = {
  program : Ast.program;
  bindings : binding list;
  declarations : declaration list;
  assignment : Solver.assignment;
  coercions : Ast.loc list;
}

type pending_binding = {
  pending_name : string;
  pending_mutable : bool;
  pending_type : Types.t;
  pending_marker : Types.t;
  pending_loc : Ast.loc;
}

type bound = { mutable_ : bool; ty : Types.t; marker : Types.t }

type row = { constraint_ : Solver.constraint_; loc : Ast.loc; reason : string }

type pending_coercion = {
  lower : Solver.term;
  upper : Solver.term;
  loc : Ast.loc;
}

type alias = { alias_parameters : string list; alias_body : Ast.ty }

type state = {
  mutable declarations : declaration String_map.t;
  mutable aliases : alias String_map.t;
  mutable variables : bound String_map.t;
  mutable pending_bindings : pending_binding list;
  mutable diagnostics : diagnostic list;
  mutable rows : row list;
  mutable coercions : pending_coercion list;
  mutable fresh_variables : (string * Ast.loc) list;
  expression_types : (int * int, Types.t) Hashtbl.t;
  mutable next_fresh : int;
  mutable next_marker : int;
}

let builtins =
  [ "Int"; "Decimal"; "String"; "Bottom"; "Set"; "List"; "Option"; "Edge";
    "UndirectedEdge"; "Graph"; "Opaque"; "Eq"; "mut" ]

let empty_state () =
  { declarations = String_map.empty;
    aliases = String_map.empty;
    variables = String_map.empty;
    pending_bindings = [];
    diagnostics = [];
    rows = [];
    coercions = [];
    fresh_variables = [];
    expression_types = Hashtbl.create 128;
    next_fresh = 0;
    next_marker = 0 }

let diagnose state loc message =
  state.diagnostics <- { loc; message } :: state.diagnostics

let key (loc : Ast.loc) = (loc.line, loc.column)

let remember state expression ty =
  Hashtbl.replace state.expression_types (key expression.Ast.loc) ty;
  ty

let expression_type state expression =
  Option.value
    (Hashtbl.find_opt state.expression_types (key expression.Ast.loc))
    ~default:Types.Error

let fresh state loc purpose =
  let name = Printf.sprintf "$%s:%d" purpose state.next_fresh in
  state.next_fresh <- state.next_fresh + 1;
  state.fresh_variables <- (name, loc) :: state.fresh_variables;
  Types.Variable name

let marker state loc purpose =
  let name =
    Printf.sprintf "$Marker:%s:%d:%d:%d" purpose loc.Ast.line loc.column
      state.next_marker
  in
  state.next_marker <- state.next_marker + 1;
  Types.Named (name, [])

let duplicate_names values =
  let counts = Hashtbl.create (List.length values) in
  List.iter
    (fun value ->
      Hashtbl.replace counts value
        (1 + Option.value (Hashtbl.find_opt counts value) ~default:0))
    values;
  Hashtbl.fold
    (fun value count output -> if count > 1 then value :: output else output)
    counts []
  |> List.sort String.compare

let validate_parameters state loc owner parameters =
  duplicate_names parameters
  |> List.iter (fun parameter ->
       diagnose state loc
         (Printf.sprintf "duplicate type parameter '%s' in %s" parameter owner));
  List.iter
    (fun parameter ->
      if List.mem parameter builtins then
        diagnose state loc
          (Printf.sprintf "type parameter '%s' shadows a built-in type" parameter))
    parameters

let parameter_map parameters arguments =
  if List.length parameters <> List.length arguments then []
  else List.combine parameters arguments

let rec resolve_type state ?(substitution = []) ?(seen = []) parameters syntax =
  let resolve = resolve_type state ~substitution ~seen parameters in
  match syntax.Ast.it with
  | Ast.TySum values -> Types.sum (List.map resolve values)
  | Ast.TyName name -> (
      match List.assoc_opt name substitution with
      | Some ty -> ty
      | None when List.mem name parameters -> Types.Parameter name
      | None -> resolve_named state ~substitution ~seen parameters syntax.loc name [])
  | Ast.TyApply (name, arguments) ->
      let arguments = List.map resolve arguments in
      resolve_named state ~substitution ~seen parameters syntax.loc name arguments

and resolve_named state ~substitution ~seen parameters loc name arguments =
  let arity expected build =
    if List.length arguments = expected then build arguments
    else (
      diagnose state loc
        (Printf.sprintf "type '%s' expects %d argument(s), got %d" name expected
           (List.length arguments));
      Types.Error)
  in
  match name with
  | "Int" -> arity 0 (fun _ -> Types.Int)
  | "Decimal" -> arity 0 (fun _ -> Types.Decimal)
  | "String" -> arity 0 (fun _ -> Types.String)
  | "Bottom" -> arity 0 (fun _ -> Types.Bottom)
  | "Set" -> arity 1 (function [ element ] -> Types.Set element | _ -> assert false)
  | "List" -> arity 1 (function [ element ] -> Types.List element | _ -> assert false)
  | "Option" -> arity 1 (function [ payload ] -> Types.Option payload | _ -> assert false)
  | "Edge" ->
      arity 3 (function
        | [ tail; head; payload ] ->
            Types.Edge (Types.Directed, tail, head, payload)
        | _ -> assert false)
  | "UndirectedEdge" ->
      arity 3 (function
        | [ left; right; payload ] ->
            Types.Edge (Types.Undirected, left, right, payload)
        | _ -> assert false)
  | "Graph" ->
      arity 3 (function
        | [ tail; head; payload ] ->
            Types.Set
              (Types.sum
                 [ Types.Edge (Types.Directed, tail, head, payload);
                   Types.Edge (Types.Undirected, tail, head, payload) ])
        | _ -> assert false)
  | "Opaque" | "Eq" | "mut" ->
      diagnose state loc ("type '" ^ name ^ "' is internal and cannot be written");
      Types.Error
  | _ -> (
      match String_map.find_opt name state.aliases with
      | Some alias ->
          if List.mem name seen then (
            diagnose state loc ("recursive type alias '" ^ name ^ "'");
            Types.Error)
          else if List.length arguments <> List.length alias.alias_parameters then (
            diagnose state loc
              (Printf.sprintf "type alias '%s' expects %d argument(s), got %d" name
                 (List.length alias.alias_parameters) (List.length arguments));
            Types.Error)
          else
            resolve_type state
              ~substitution:(parameter_map alias.alias_parameters arguments @ substitution)
              ~seen:(name :: seen) parameters alias.alias_body
      | None -> (
          match String_map.find_opt name state.declarations with
          | None ->
              diagnose state loc ("unknown type '" ^ name ^ "'");
              Types.Error
          | Some declaration ->
              if List.length arguments <> List.length declaration.parameters then (
                diagnose state loc
                  (Printf.sprintf "type '%s' expects %d argument(s), got %d" name
                     (List.length declaration.parameters) (List.length arguments));
                Types.Error)
              else declaration_type state declaration arguments))

and declaration_type state declaration arguments =
  let substitution = parameter_map declaration.parameters arguments in
  Types.Named
    (declaration.name,
     List.map
       (fun (label, syntax) ->
         (label,
          resolve_type state ~substitution declaration.parameters syntax))
       declaration.members)

let add_row state loc reason constraint_ =
  state.rows <- { constraint_; loc; reason } :: state.rows

let equal_constraint state loc reason left right =
  if left = Types.Error || right = Types.Error || Types.equal left right then ()
  else if not (Types.has_variable left || Types.has_variable right) then
    diagnose state loc
      (Printf.sprintf "%s: %s is not equal to %s" reason (Types.pretty left)
         (Types.pretty right))
  else
    add_row state loc reason
      (Solver.Equal (Types.to_solver left, Types.to_solver right))

let compatible_edge_parameters state loc left_tail left_head left_payload
    right_tail right_head right_payload =
  equal_constraint state loc "edge tail types differ" left_tail right_tail;
  equal_constraint state loc "edge head types differ" left_head right_head;
  equal_constraint state loc "edge payload types differ" left_payload right_payload

let add_coercion state loc actual expected =
  state.coercions <-
    { lower = Types.to_solver actual; upper = Types.to_solver expected; loc }
    :: state.coercions

(* A sum describes the alternatives contributed by a distributive container;
   it is not a union type for an individual value.  Keep this relation
   separate from [Types.below], which is the underlying ACUIhE order and does
   make every summand lie below its sum. *)
let combine_constructibility relations =
  if List.exists (( = ) Types.No) relations then Types.No
  else if List.exists (( = ) Types.Deferred) relations then Types.Deferred
  else Types.Yes

let choose_constructibility relations =
  if List.exists (( = ) Types.Yes) relations then Types.Yes
  else if List.exists (( = ) Types.Deferred) relations then Types.Deferred
  else Types.No

let rec constructible_below ~sum_position actual expected =
  if Types.equal actual expected || actual = Types.Error || expected = Types.Error
  then Types.Yes
  else
    match (actual, expected) with
    | Types.Variable _, _ | _, Types.Variable _ -> Types.Deferred
    | Types.Bottom, _ -> Types.Yes
    | _, Types.Sum choices when sum_position ->
        Types.summands actual
        |> List.map (fun value ->
             choices
             |> List.map (constructible_below ~sum_position:false value)
             |> choose_constructibility)
        |> combine_constructibility
    | Types.Sum values, _ when sum_position ->
        values
        |> List.map (fun value ->
             constructible_below ~sum_position:false value expected)
        |> combine_constructibility
    | _, Types.Sum _ | Types.Sum _, _ -> Types.No
    | Types.Set actual, Types.Set expected ->
        constructible_below ~sum_position:true actual expected
    | Types.List actual, Types.List expected ->
        constructible_below ~sum_position:true actual expected
    | Types.Option actual, Types.Option expected ->
        constructible_below ~sum_position:false actual expected
    | Types.Edge (actual_kind, actual_tail, actual_head, actual_payload),
      Types.Edge (expected_kind, expected_tail, expected_head, expected_payload)
      when actual_kind = expected_kind ->
        combine_constructibility
          [ constructible_below ~sum_position:true actual_tail expected_tail;
            constructible_below ~sum_position:true actual_head expected_head;
            constructible_below ~sum_position:false actual_payload expected_payload ]
    | Types.Named (actual_name, actual_members),
      Types.Named (expected_name, expected_members)
      when actual_name = expected_name
           && List.length actual_members = List.length expected_members
           && List.for_all2
                (fun (actual_label, _) (expected_label, _) ->
                  actual_label = expected_label)
                actual_members expected_members ->
        List.map2
          (fun (_, actual) (_, expected) ->
            constructible_below ~sum_position:false actual expected)
          actual_members expected_members
        |> combine_constructibility
    | Types.Opaque (actual_hidden, actual_marker),
      Types.Opaque (expected_hidden, expected_marker) ->
        combine_constructibility
          [ constructible_below ~sum_position:false actual_hidden expected_hidden;
            constructible_below ~sum_position:false actual_marker expected_marker ]
    | _ -> Types.No

let rec constrain_types ?(sum_position = false) state loc actual expected reason =
  if actual = Types.Error || expected = Types.Error || Types.equal actual expected then ()
  else
    match (actual, expected) with
    | Types.Bottom, Types.Variable _ -> ()
    | Types.Variable _, _ | _, Types.Variable _ ->
        equal_constraint state loc reason actual expected
    | Types.Sum values, _
      when sum_position
           && (match expected with Types.Sum _ -> false | _ -> true) ->
        List.iter
          (fun actual -> constrain_types state loc actual expected reason)
          values
    | Types.Set actual, Types.Set expected ->
        constrain_types ~sum_position:true state loc actual expected reason
    | Types.List actual, Types.List expected ->
        constrain_types ~sum_position:true state loc actual expected reason
    | Types.Option actual, Types.Option expected ->
        constrain_types state loc actual expected reason
    | Types.Edge (actual_kind, actual_tail, actual_head, actual_payload),
      Types.Edge (expected_kind, expected_tail, expected_head, expected_payload)
      when actual_kind = expected_kind ->
        constrain_types ~sum_position:true state loc actual_tail expected_tail reason;
        constrain_types ~sum_position:true state loc actual_head expected_head reason;
        constrain_types state loc actual_payload expected_payload reason
    | Types.Named (actual_name, actual_members),
      Types.Named (expected_name, expected_members)
      when actual_name = expected_name
           && List.length actual_members = List.length expected_members
           && List.for_all2
                (fun (actual_label, _) (expected_label, _) ->
                  actual_label = expected_label)
                actual_members expected_members ->
        List.iter2
          (fun (_, actual) (_, expected) ->
            constrain_types state loc actual expected reason)
          actual_members expected_members
    | Types.Opaque (actual_hidden, actual_marker),
      Types.Opaque (expected_hidden, expected_marker) ->
        constrain_types state loc actual_hidden expected_hidden reason;
        constrain_types state loc actual_marker expected_marker reason
    | _ -> (
        match constructible_below ~sum_position actual expected with
        | Types.No ->
            diagnose state loc
              (Printf.sprintf "%s: found %s, expected %s" reason
                 (Types.pretty actual) (Types.pretty expected))
        | Types.Yes -> ()
        | Types.Deferred ->
            add_row state loc reason
              (Solver.Below (Types.to_solver actual, Types.to_solver expected)))

let rec constrain ?(sum_position = false) state expression actual expected reason =
  match (actual, expected, expression.Ast.it) with
  | Types.Set _, Types.Set expected_element, Ast.Set elements ->
      List.iter
        (fun element ->
          let actual_element = expression_type state element in
          let expected_element =
            match (actual_element, expected_element) with
            | Types.Edge (Types.Undirected, _, _, _),
              Types.Edge (Types.Directed, _, _, _) -> Types.Set expected_element
            | _ -> expected_element
          in
          constrain ~sum_position:true state element actual_element expected_element
            reason)
        elements
  | Types.List _, Types.List expected_element, Ast.List elements ->
      List.iter
        (fun element ->
          let actual_element = expression_type state element in
          constrain ~sum_position:true state element actual_element expected_element
            reason)
        elements
  | Types.Edge (Types.Undirected, left_tail, left_head, left_payload),
    Types.Set
      (Types.Edge (Types.Directed, right_tail, right_head, right_payload)), _ ->
      compatible_edge_parameters state expression.loc left_tail left_head left_payload
        right_tail right_head right_payload;
      add_coercion state expression.loc actual expected
  | _ ->
      constrain_types ~sum_position state expression.loc actual expected reason

let instantiate state loc parameters explicit =
  match explicit with
  | None -> List.map (fun parameter -> fresh state loc parameter) parameters
  | Some arguments ->
      if List.length parameters <> List.length arguments then (
        diagnose state loc
          (Printf.sprintf "expected %d type argument(s), got %d"
             (List.length parameters) (List.length arguments));
        List.map (fun parameter -> fresh state loc parameter) parameters)
      else
        List.map2
          (fun parameter -> function
            | Some syntax -> resolve_type state [] syntax
            | None -> fresh state loc parameter)
          parameters arguments

let marker_for_expression state expression =
  match expression.Ast.it with
  | Ast.Ref name -> (
      match String_map.find_opt name state.variables with
      | Some binding -> binding.marker
      | None -> marker state expression.loc "unbound")
  | _ -> marker state expression.loc "value"

let protect_for_equality state expression ty =
  Types.protect_graphs (marker_for_expression state expression) ty

let rec infer state expression =
  let inferred =
    match expression.Ast.it with
    | Ast.Int _ -> Types.Int
    | Ast.Decimal _ -> Types.Decimal
    | Ast.String _ -> Types.String
    | Ast.Ref name -> infer_reference state expression name
    | Ast.Set elements ->
        Types.Set
          (Types.sum
             (List.map
                (fun element ->
                  infer state element |> protect_for_equality state element)
                elements))
    | Ast.List elements ->
        Types.List
          (Types.sum
             (List.map
                (fun element ->
                  infer state element |> protect_for_equality state element)
                elements))
    | Ast.SetOp (operator, operands) -> infer_operation state expression operator operands
    | Ast.Edge (tail, head, payload) ->
        infer_edge state expression Types.Directed tail head payload
    | Ast.UndirectedEdge (left, right, payload) ->
        infer_edge state expression Types.Undirected left right payload
    | Ast.Apply (name, explicit, arguments) ->
        infer_application state expression name explicit arguments
    | Ast.Variant (enum_name, variant_name, arguments) ->
        infer_variant state expression enum_name variant_name arguments
  in
  remember state expression inferred

and infer_reference state expression name =
  match String_map.find_opt name state.variables with
  | Some binding -> binding.ty
  | None when name = "None" -> infer_variant state expression "Option" "None" []
  | None ->
      diagnose state expression.loc ("undefined variable '" ^ name ^ "'");
      Types.Error

and infer_edge state expression kind left right payload =
  let left_type = infer state left and right_type = infer state right in
  let side label side expression_type =
    match Types.as_set expression_type with
    | Some element -> element
    | None ->
        diagnose state side.Ast.loc
          (Printf.sprintf "%s of edge has type %s, expected a Set<...>" label
             (Types.pretty expression_type));
        Types.Error
  in
  let tail = side "left side" left left_type in
  let head = side "right side" right right_type in
  let payload =
    match payload with
    | None -> Types.Bottom
    | Some payload -> infer state payload |> protect_for_equality state payload
  in
  ignore expression;
  Types.Edge (kind, tail, head, payload)

and infer_application state expression name explicit arguments =
  if name = "Some" then infer_variant state expression "Option" "Some" arguments
  else
    match String_map.find_opt name state.declarations with
    | Some ({ kind = Struct_kind; _ } as declaration) ->
        let parameters = instantiate state expression.loc declaration.parameters explicit in
        let substitution = parameter_map declaration.parameters parameters in
        let fields = declaration.members in
        if List.length fields <> List.length arguments then
          diagnose state expression.loc
            (Printf.sprintf "struct %s expects %d value argument(s), got %d" name
               (List.length fields) (List.length arguments));
        List.iter2
          (fun (label, syntax) argument ->
            let actual = infer state argument in
            let expected =
              resolve_type state ~substitution declaration.parameters syntax
            in
            constrain state argument actual expected ("field '" ^ label ^ "'"))
          (List.filteri (fun index _ -> index < List.length arguments) fields)
          (List.filteri (fun index _ -> index < List.length fields) arguments);
        declaration_type state declaration parameters
    | Some _ ->
        diagnose state expression.loc
          ("'" ^ name ^ "' is an enum; construct a variant with " ^ name ^ "::Variant");
        Types.Error
    | None ->
        diagnose state expression.loc ("unknown struct constructor '" ^ name ^ "'");
        Types.Error

and infer_variant state expression enum_name variant_name arguments =
  if enum_name = "Option" then
    let parameter = fresh state expression.loc "Option" in
    (match variant_name with
     | "Some" ->
         if List.length arguments <> 1 then
           diagnose state expression.loc
             (Printf.sprintf "Option::Some expects 1 argument, got %d"
                (List.length arguments));
         Option.iter
           (fun argument ->
             let actual = infer state argument in
             constrain state argument actual parameter "Option::Some payload")
           (List.nth_opt arguments 0)
     | "None" ->
         if arguments <> [] then
           diagnose state expression.loc "Option::None does not take arguments"
     | _ -> diagnose state expression.loc ("unknown Option variant '" ^ variant_name ^ "'"));
    Types.Option parameter
  else
    match String_map.find_opt enum_name state.declarations with
    | Some ({ kind = Enum_kind; _ } as declaration) ->
        let parameters = instantiate state expression.loc declaration.parameters None in
        let substitution = parameter_map declaration.parameters parameters in
        let prefix = variant_name ^ ":" in
        let payload =
          List.filter
            (fun (label, _) ->
              label = variant_name
              || (String.length label >= String.length prefix
                 && String.sub label 0 (String.length prefix) = prefix))
            declaration.members
        in
        let constructor_payload =
          match payload with
          | [ (label, { Ast.it = Ast.TyName "Bottom"; _ }) ]
            when label = variant_name -> []
          | payload -> payload
        in
        if payload = [] then
          diagnose state expression.loc
            (Printf.sprintf "enum %s has no variant '%s'" enum_name variant_name)
        else (
          if List.length constructor_payload <> List.length arguments then
            diagnose state expression.loc
              (Printf.sprintf "%s::%s expects %d argument(s), got %d" enum_name
                 variant_name (List.length constructor_payload) (List.length arguments));
          List.iter2
            (fun (_, syntax) argument ->
              let actual = infer state argument in
              let expected =
                resolve_type state ~substitution declaration.parameters syntax
              in
              constrain state argument actual expected
                (enum_name ^ "::" ^ variant_name ^ " payload"))
            (List.filteri
               (fun index _ -> index < List.length arguments)
               constructor_payload)
            (List.filteri
               (fun index _ -> index < List.length constructor_payload)
               arguments));
        declaration_type state declaration parameters
    | Some _ ->
        diagnose state expression.loc ("'" ^ enum_name ^ "' is not an enum");
        Types.Error
    | None ->
        diagnose state expression.loc ("unknown enum '" ^ enum_name ^ "'");
        Types.Error

and infer_operation state expression operator operands =
  let types = List.map (infer state) operands in
  let as_set operand ty =
    match ty with
    | Types.Set element -> Some element
    | Types.Edge (Types.Undirected, tail, head, payload) ->
        let upper =
          Types.Set (Types.Edge (Types.Directed, tail, head, payload))
        in
        add_coercion state operand.Ast.loc ty upper;
        Some (Types.Edge (Types.Directed, tail, head, payload))
    | _ -> None
  in
  let set_types = List.map2 as_set operands types in
  if List.for_all Option.is_some set_types then
    let elements = List.map Option.get set_types in
    (match elements with
     | [] -> Types.Set Types.Bottom
     | first :: rest ->
         Types.Set (List.fold_left (Types.apply_set_operator operator) first rest))
  else
    match types with
    | Types.Edge (kind, tail, head, payload) :: rest
      when List.for_all
             (function Types.Edge (other, _, _, _) -> kind = other | _ -> false)
             rest ->
        List.fold_left
          (fun accumulated next ->
            match (accumulated, next) with
            | Types.Edge (kind, left_tail, left_head, left_payload),
              Types.Edge (_, right_tail, right_head, right_payload) ->
                equal_constraint state expression.loc
                  "edge surgery requires equal payload types" left_payload right_payload;
                Types.Edge
                  (kind,
                   Types.apply_set_operator operator left_tail right_tail,
                   Types.apply_set_operator operator left_head right_head,
                   left_payload)
            | _ -> Types.Error)
          (Types.Edge (kind, tail, head, payload)) rest
    | _ ->
        diagnose state expression.loc
          ("operator '" ^ Ast.op_symbol operator
         ^ "' requires only sets or only edges of the same kind");
        Types.Error

let valid_new_name state loc name kind =
  if List.mem name builtins then (
    diagnose state loc (kind ^ " name '" ^ name ^ "' is reserved");
    false)
  else if String_map.mem name state.declarations || String_map.mem name state.aliases then (
    diagnose state loc ("duplicate type declaration '" ^ name ^ "'");
    false)
  else true

let declare_struct state statement name parameters fields =
  validate_parameters state statement.Ast.loc ("struct " ^ name) parameters;
  duplicate_names (List.map (fun field -> field.Ast.field_name) fields)
  |> List.iter (fun field ->
       diagnose state statement.loc ("duplicate field '" ^ field ^ "' in struct " ^ name));
  let declaration =
    { kind = Struct_kind;
      name;
      parameters;
      members = List.map (fun field -> (field.Ast.field_name, field.field_type)) fields;
      resolved_members = [] }
  in
  let accepted = valid_new_name state statement.loc name "struct" in
  if accepted then
    state.declarations <- String_map.add name declaration state.declarations;
  let resolved_members =
    List.map
      (fun field ->
        (field.Ast.field_name,
         resolve_type state parameters field.Ast.field_type))
      fields
  in
  if accepted then
    state.declarations <-
      String_map.add name { declaration with resolved_members } state.declarations

let declare_enum state statement name parameters variants =
  validate_parameters state statement.Ast.loc ("enum " ^ name) parameters;
  duplicate_names (List.map (fun variant -> variant.Ast.variant_name) variants)
  |> List.iter (fun variant ->
       diagnose state statement.loc ("duplicate variant '" ^ variant ^ "' in enum " ^ name));
  let members =
    List.concat_map
      (fun variant ->
        match variant.Ast.variant_payload with
        | [] -> [ (variant.variant_name, Ast.at variant.variant_loc (Ast.TyName "Bottom")) ]
        | payload ->
            List.mapi
              (fun index ty -> (Printf.sprintf "%s:%d" variant.variant_name index, ty))
              payload)
      variants
  in
  let declaration =
    { kind = Enum_kind; name; parameters; members; resolved_members = [] }
  in
  let accepted = valid_new_name state statement.loc name "enum" in
  if accepted then
    state.declarations <- String_map.add name declaration state.declarations;
  let resolved_members =
    List.map
      (fun (label, ty) -> (label, resolve_type state parameters ty))
      members
  in
  if accepted then
    state.declarations <-
      String_map.add name { declaration with resolved_members } state.declarations

let declare_alias state statement name parameters body =
  validate_parameters state statement.Ast.loc ("alias " ^ name) parameters;
  if valid_new_name state statement.loc name "alias" then (
    ignore (resolve_type state parameters body);
    state.aliases <-
      String_map.add name { alias_parameters = parameters; alias_body = body }
        state.aliases)

let combine_update state loc operator left right =
  match (left, right) with
  | Types.Set left, Types.Set right ->
      Types.Set (Types.apply_set_operator operator left right)
  | Types.Edge (kind, left_tail, left_head, left_payload),
    Types.Edge (other, right_tail, right_head, right_payload)
    when kind = other ->
      equal_constraint state loc "edge surgery requires equal payload types" left_payload
        right_payload;
      Types.Edge
        (kind, Types.apply_set_operator operator left_tail right_tail,
         Types.apply_set_operator operator left_head right_head, left_payload)
  | _ ->
      diagnose state loc
        ("operator '" ^ Ast.op_symbol operator
       ^ "=' requires matching set or edge operands");
      Types.Error

let check_statement state statement =
  match statement.Ast.it with
  | Ast.Struct (name, parameters, fields) ->
      declare_struct state statement name parameters fields
  | Ast.Enum (name, parameters, variants) ->
      declare_enum state statement name parameters variants
  | Ast.Alias (name, parameters, body) ->
      declare_alias state statement name parameters body
  | Ast.Let (name, annotation, expression) ->
      let actual = infer state expression in
      let mutable_, ty =
        match annotation with
        | None -> (false, actual)
        | Some annotation ->
            let expected = resolve_type state [] annotation.Ast.ty in
            constrain state expression actual expected ("binding '" ^ name ^ "'");
            (annotation.mutable_, expected)
      in
      if String_map.mem name state.variables then
        diagnose state statement.loc ("duplicate binding '" ^ name ^ "'")
      else
        let marker =
          match expression.Ast.it with
          | Ast.Ref source -> (
              match String_map.find_opt source state.variables with
              | Some binding -> binding.marker
              | None -> marker state statement.loc ("binding:" ^ name))
          | _ -> marker state statement.loc ("binding:" ^ name)
        in
        state.variables <- String_map.add name { mutable_; ty; marker } state.variables;
        state.pending_bindings <-
          { pending_name = name;
            pending_mutable = mutable_;
            pending_type = ty;
            pending_marker = marker;
            pending_loc = statement.loc }
          :: state.pending_bindings
  | Ast.Update (name, operator, expression) -> (
      let right = infer state expression in
      match String_map.find_opt name state.variables with
      | None -> diagnose state statement.loc ("undefined variable '" ^ name ^ "'")
      | Some binding ->
          if not binding.mutable_ then
            diagnose state statement.loc ("binding '" ^ name ^ "' is immutable");
          let right =
            match (binding.ty, right) with
            | Types.Set _, Types.Edge (Types.Undirected, tail, head, payload) ->
                let upper =
                  Types.Set (Types.Edge (Types.Directed, tail, head, payload))
                in
                add_coercion state expression.loc right upper;
                upper
            | _ -> right
          in
          let updated = combine_update state statement.loc operator binding.ty right in
          constrain state expression updated binding.ty ("update of '" ^ name ^ "'"))

let solver_error loc message = [ { loc; message } ]

let run_solver state =
  let origin =
    match state.rows with
    | row :: _ -> row.loc
    | [] -> (match state.fresh_variables with (_, loc) :: _ -> loc | [] -> Ast.{ line = 1; column = 1 })
  in
  let base_rows = state.rows in
  let base_constraints = List.map (fun row -> row.constraint_) base_rows in
  match Solver.solve base_constraints with
  | Error error -> Error (solver_error origin ("verified solver error: " ^ error.message))
  | Ok Solver.Unsat ->
      let reasons =
        base_rows |> List.map (fun row -> row.reason) |> List.sort_uniq String.compare
      in
      Error
        (solver_error origin
           ("type constraints are inconsistent"
           ^ (if reasons = [] then "" else ": " ^ String.concat "; " reasons)))
  | Ok (Solver.Sat preliminary) ->
      let preliminary =
        List.fold_left
          (fun assignment (name, _) ->
            if List.mem_assoc name assignment then assignment
            else (name, Solver.bottom) :: assignment)
          preliminary state.fresh_variables
      in
      if state.coercions = [] then Ok preliminary
      else
        let rules =
          List.map
            (fun coercion ->
              let lower = Solver.substitute preliminary coercion.lower in
              let upper = Solver.substitute preliminary coercion.upper in
              Solver.of_subsumption ~lower ~upper)
            state.coercions
        in
        match Solver.solve ~rules [] with
        | Error error ->
            Error (solver_error origin ("verified solver error: " ^ error.message))
        | Ok Solver.Unsat ->
            Error
              (solver_error origin
                 "the specialized UndirectedEdge-to-Set<Edge> coercion is inconsistent")
        | Ok (Solver.Sat _) -> Ok preliminary

let check program =
  let state = empty_state () in
  List.iter (check_statement state) program;
  match List.rev state.diagnostics with
  | _ :: _ as diagnostics -> Error diagnostics
  | [] -> (
      match run_solver state with
      | Error diagnostics -> Error diagnostics
      | Ok assignment ->
          let bindings =
            List.rev state.pending_bindings
            |> List.map (fun pending ->
                 { name = pending.pending_name;
                   mutable_ = pending.pending_mutable;
                   ty = pending.pending_type;
                   solved_type =
                     Solver.substitute assignment (Types.to_solver pending.pending_type);
                   marker = pending.pending_marker;
                   loc = pending.pending_loc })
          in
          Ok
            { program;
              bindings;
              declarations =
                String_map.bindings state.declarations |> List.map snd;
              assignment;
              coercions =
                state.coercions |> List.map (fun coercion -> coercion.loc)
                |> List.sort_uniq compare })

let find_binding checked name =
  List.find_opt (fun binding -> binding.name = name) checked.bindings

let pp_solved_type formatter binding = Solver.pp_term formatter binding.solved_type
