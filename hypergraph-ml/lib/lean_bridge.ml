type error = { message : string }

external invoke_raw : string -> string = "caml_hypergraphml_bridge"

let invoke request =
  let response = invoke_raw (Yojson.Safe.to_string request) in
  match Yojson.Safe.from_string response with
  | exception Yojson.Json_error message -> Error { message }
  | `Assoc fields as json -> (
      match List.assoc_opt "status" fields with
      | Some (`String "error") ->
          let message =
            match List.assoc_opt "message" fields with
            | Some (`String message) -> message
            | _ -> "Lean bridge returned an error without a message"
          in
          Error { message }
      | _ -> Ok json)
  | _ -> Error { message = "Lean bridge returned a non-object response" }

