%{
open Ast

let loc_of (position : Lexing.position) : loc =
  { line = position.pos_lnum; column = position.pos_cnum - position.pos_bol + 1 }

let located position it = { it; loc = loc_of position }

let sum position = function
  | [single] -> single
  | summands -> located position (TySum summands)

let chain position first rest =
  match rest with
  | [] -> first
  | (operator, _, _) :: _ ->
      List.iter
        (fun (next, at, _) ->
          if next <> operator then raise (Mixed_ops (operator, next, at)))
        rest;
      located position
        (SetOp (operator, first :: List.map (fun (_, _, value) -> value) rest))
%}

%token <Z.t> INT
%token <Q.t> DECIMAL
%token <string> STRING IDENT
%token LET STRUCT ENUM ALIAS MUT
%token LBRACE RBRACE LPAREN RPAREN LT GT
%token COMMA COLON DCOLON EQUALS PLUS UNDERSCORE
%token BAR AMP MINUS BAR_EQ AMP_EQ MINUS_EQ
%token ARROW_R ARROW_L ARROW_LR
%token ANN_L ANN_R BANN_L BANN_R
%token NEWLINE EOF

%start <Ast.program> program
%start <Ast.stmt> line

%%

program: newlines; statements = statements; EOF { statements }
line: newlines; statement = statement; newlines; EOF { statement }

statements:
  |                                                    { [] }
  | statement = statement; rest = after_statement     { statement :: rest }

after_statement:
  |                                                    { [] }
  | newlines1; rest = statements                       { rest }

newlines: list(NEWLINE)                                { () }
newlines1: nonempty_list(NEWLINE)                      { () }

statement:
  | LET; name = IDENT; annotation = option(annotation); EQUALS; value = expression
      { located $startpos (Let (name, annotation, value)) }
  | name = IDENT; operator = update_operator; value = expression
      { located $startpos (Update (name, operator, value)) }
  | STRUCT; name = IDENT; parameters = loption(parameters);
      LBRACE; newlines; fields = fields; RBRACE
      { located $startpos (Struct (name, parameters, fields)) }
  | ENUM; name = IDENT; parameters = loption(parameters);
      LBRACE; newlines; variants = variants; RBRACE
      { located $startpos (Enum (name, parameters, variants)) }
  | ALIAS; name = IDENT; parameters = loption(parameters); EQUALS; body = type_sum
      { located $startpos (Alias (name, parameters, body)) }

annotation:
  | COLON; mutable_ = boption(MUT); ty = type_sum       { { mutable_; ty } }

parameters:
  | LT; values = separated_nonempty_list(COMMA, IDENT); GT { values }

fields:
  |                                                    { [] }
  | field = field; rest = field_tail                   { field :: rest }

field_tail:
  | newlines                                           { [] }
  | newlines; COMMA; newlines                          { [] }
  | newlines; COMMA; newlines; field = field; rest = field_tail
                                                       { field :: rest }

field:
  | name = IDENT; COLON; ty = type_sum
      { { field_name = name; field_type = ty; field_loc = loc_of $startpos } }

variants:
  |                                                    { [] }
  | variant = variant; rest = variant_tail             { variant :: rest }

variant_tail:
  | newlines                                           { [] }
  | newlines; COMMA; newlines                          { [] }
  | newlines; COMMA; newlines; variant = variant; rest = variant_tail
                                                       { variant :: rest }

variant:
  | name = IDENT
      { { variant_name = name; variant_payload = []; variant_loc = loc_of $startpos } }
  | name = IDENT; LPAREN; payload = separated_nonempty_list(COMMA, type_sum); RPAREN
      { { variant_name = name; variant_payload = payload;
          variant_loc = loc_of $startpos } }

type_sum:
  | values = separated_nonempty_list(PLUS, type_atom)  { sum $startpos values }

type_atom:
  | name = IDENT                                       { located $startpos (TyName name) }
  | name = IDENT; LT; arguments = separated_nonempty_list(COMMA, type_sum); GT
                                                       { located $startpos (TyApply (name, arguments)) }
  | LPAREN; ty = type_sum; RPAREN                      { ty }

expression:
  | tail = set_expression; ARROW_R; head = set_expression
      { located $startpos (Edge (tail, head, None)) }
  | head = set_expression; ARROW_L; tail = set_expression
      { located $startpos (Edge (tail, head, None)) }
  | left = set_expression; ARROW_LR; right = set_expression
      { located $startpos (UndirectedEdge (left, right, None)) }
  | tail = set_expression; ANN_L; payload = expression; ANN_R; head = set_expression
      { located $startpos (Edge (tail, head, Some payload)) }
  | head = set_expression; BANN_L; payload = expression; BANN_R; tail = set_expression
      { located $startpos (Edge (tail, head, Some payload)) }
  | left = set_expression; BANN_L; payload = expression; ANN_R; right = set_expression
      { located $startpos (UndirectedEdge (left, right, Some payload)) }
  | value = value                                      { value }

value:
  | value = INT                                        { located $startpos (Int value) }
  | MINUS; value = INT                                 { located $startpos (Int (Z.neg value)) }
  | value = DECIMAL                                    { located $startpos (Decimal value) }
  | MINUS; value = DECIMAL                             { located $startpos (Decimal (Q.neg value)) }
  | value = STRING                                     { located $startpos (String value) }
  | enum_name = IDENT; DCOLON; variant_name = IDENT; arguments = option(call_arguments)
      { located $startpos
          (Variant (enum_name, variant_name, Option.value arguments ~default:[])) }
  | name = IDENT; type_arguments = option(type_arguments); arguments = call_arguments
      { located $startpos (Apply (name, type_arguments, arguments)) }
  | value = set_expression                             { value }

type_arguments:
  | LT; arguments = separated_nonempty_list(COMMA, type_argument); GT { arguments }

type_argument:
  | ty = type_sum                                      { Some ty }
  | UNDERSCORE                                         { None }

call_arguments:
  | LPAREN; arguments = separated_list(COMMA, expression); RPAREN { arguments }

set_expression:
  | first = set_atom; rest = list(chained_set_atom)    { chain $startpos first rest }

chained_set_atom:
  | operator = set_operator; value = set_atom          { (operator, loc_of $startpos, value) }

set_operator:
  | BAR                                                { Union }
  | AMP                                                { Intersection }
  | MINUS                                              { Difference }

update_operator:
  | BAR_EQ                                             { Union }
  | AMP_EQ                                             { Intersection }
  | MINUS_EQ                                           { Difference }

set_atom:
  | LBRACE; newlines; elements = elements; RBRACE
      { located $startpos (Set elements) }
  | name = IDENT                                       { located $startpos (Ref name) }
  | LPAREN; value = expression; RPAREN                 { value }

elements:
  |                                                    { [] }
  | value = expression; rest = element_tail            { value :: rest }

element_tail:
  | newlines                                           { [] }
  | newlines; COMMA; newlines                          { [] }
  | newlines; COMMA; newlines; value = expression; rest = element_tail
                                                       { value :: rest }
