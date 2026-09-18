%{
open Ast
open Location
%}

%token STRUCT "struct" ENUM "enum" ALIAS "alias" LET "let" MUT "mut"
%token <string> IDENT INT DECIMAL STRING
%token LBRACE "{" RBRACE "}" LBRACKET "[" RBRACKET "]"
%token LPAREN "(" RPAREN ")" LT "<" GT ">"
%token COLON ":" COMMA "," SEMICOLON ";" EQUAL "=" DCOLON "::"
%token PLUS "+" BANG "!" PIPE "|" AMP "&" MINUS "-"
%token PIPE_EQUAL "|=" AMP_EQUAL "&=" MINUS_EQUAL "-="
%token RIGHT_ARROW "->" LEFT_ARROW "<-" BOTH_ARROW "<->"
%token RIGHT_PAYLOAD "-[" LEFT_PAYLOAD "<-["
%token EOF

%start <Ast.program> program
%start <Ast.expr> expression
%start <Ast.typ> type_expression

%%

program:
  | statements = list(terminated(statement, option(SEMICOLON))) EOF
      { statements }

expression:
  | value = expr EOF { value }

type_expression:
  | value = typ EOF { value }

identifier:
  | name = IDENT { located $startpos $endpos name }

parameters:
  | { [] }
  | LT names = comma_nonempty(identifier) GT { names }

statement:
  | STRUCT name = identifier parameters = parameters
    LBRACE fields = comma_list(field) RBRACE
      { located $startpos $endpos (Struct { name; parameters; fields }) }
  | ENUM name = identifier parameters = parameters
    LBRACE variants = comma_list(variant) RBRACE
      { located $startpos $endpos (Enum { name; parameters; variants }) }
  | ALIAS name = identifier parameters = parameters EQUAL body = typ
      { located $startpos $endpos (Alias { name; parameters; body }) }
  | LET name = identifier annotation = annotation EQUAL value = expr
      { let mutable_, annotation = annotation in
        located $startpos $endpos (Let { name; mutable_; annotation; value }) }
  | name = identifier operator = update_operator value = expr
      { located $startpos $endpos (Update { name; operator; value }) }

annotation:
  | { (false, None) }
  | COLON mutable_ = boption(MUT) typ = typ { (mutable_, Some typ) }

field:
  | field_name = identifier COLON field_type = typ
      { { field_name; field_type; loc = make $startpos $endpos } }

variant:
  | variant_name = identifier arguments = option(delimited(LPAREN, comma_list(typ), RPAREN))
      { { variant_name; arguments; loc = make $startpos $endpos } }

typ:
  | typ = atomic_type { typ }
  | left = typ PLUS right = atomic_type
      { located $startpos $endpos (Sum_type (left, right)) }

atomic_type:
  | name = identifier arguments = type_arguments
      { located $startpos $endpos (Named_type (name, arguments)) }
  | BANG
      { let name = located $startpos $endpos "Bottom" in
        located $startpos $endpos (Named_type (name, [])) }
  | LPAREN typ = typ RPAREN { { typ with loc = make $startpos $endpos } }

type_arguments:
  | { [] }
  | LT arguments = comma_nonempty(typ) GT { arguments }

(* Arrows have the lowest precedence and do not associate. Parentheses are
   required when an edge is itself an endpoint of another edge. *)
expr:
  | value = union_expr { value }
  | left = union_expr direction = plain_arrow right = union_expr
      { located $startpos $endpos (Edge { direction; left; right; payload = None }) }
  | left = union_expr RIGHT_PAYLOAD payload = expr RBRACKET RIGHT_ARROW right = union_expr
      { located $startpos $endpos
          (Edge { direction = Forward; left; right; payload = Some payload }) }
  | left = union_expr LEFT_PAYLOAD payload = expr RBRACKET direction = payload_end right = union_expr
      { located $startpos $endpos (Edge { direction; left; right; payload = Some payload }) }

plain_arrow:
  | RIGHT_ARROW { Forward }
  | LEFT_ARROW { Backward }
  | BOTH_ARROW { Undirected }

payload_end:
  | MINUS { Backward }
  | RIGHT_ARROW { Undirected }

union_expr:
  | value = intersection_expr { value }
  | left = union_expr PIPE right = intersection_expr
      { located $startpos $endpos (Binary (Union, left, right)) }
  | left = union_expr MINUS right = intersection_expr
      { located $startpos $endpos (Binary (Difference, left, right)) }

intersection_expr:
  | value = atom { value }
  | left = intersection_expr AMP right = atom
      { located $startpos $endpos (Binary (Intersection, left, right)) }

atom:
  | value = INT { located $startpos $endpos (Int value) }
  | MINUS value = INT { located $startpos $endpos (Int ("-" ^ value)) }
  | value = DECIMAL { located $startpos $endpos (Decimal value) }
  | MINUS value = DECIMAL { located $startpos $endpos (Decimal ("-" ^ value)) }
  | value = STRING { located $startpos $endpos (String value) }
  | name = identifier { located $startpos $endpos (Name name) }
  | name = identifier LPAREN arguments = comma_list(expr) RPAREN
      { located $startpos $endpos (Construct (name, arguments)) }
  | name = identifier DCOLON variant = identifier
    arguments = option(delimited(LPAREN, comma_list(expr), RPAREN))
      { located $startpos $endpos (Variant (name, variant, arguments)) }
  | LBRACE values = comma_list(expr) RBRACE
      { located $startpos $endpos (Set values) }
  | LBRACKET values = comma_list(expr) RBRACKET
      { located $startpos $endpos (List values) }
  | LPAREN value = expr RPAREN { { value with loc = make $startpos $endpos } }

update_operator:
  | PIPE_EQUAL { Union }
  | AMP_EQUAL { Intersection }
  | MINUS_EQUAL { Difference }

(* This formulation permits one trailing comma without a shift/reduce conflict. *)
comma_list(X):
  | { [] }
  | values = comma_nonempty(X) { values }

comma_nonempty(X):
  | value = X { [value] }
  | value = X COMMA rest = comma_list(X) { value :: rest }
