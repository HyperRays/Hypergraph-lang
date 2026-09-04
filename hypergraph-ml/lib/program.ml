type error =
  | Parse_error of Driver.error
  | Type_errors of Check.diagnostic list
  | Evaluation_error of Value.error

type result = { checked : Check.checked; values : Value.environment }

let run source =
  match Driver.parse source with
  | Error error -> Error (Parse_error error)
  | Ok program -> (
      match Check.check program with
      | Error diagnostics -> Error (Type_errors diagnostics)
      | Ok checked -> (
          match Value.run checked with
          | Error error -> Error (Evaluation_error error)
          | Ok values -> Ok { checked; values }))
