type typevariant = Variant of (string * string list)
type typedVariable = TypedVariable of (string * string)

type pattern
= Constructor of (string * pattern list) (* constructor name, arguments *)
| Variable of (string * string) (* variable name, type name *)

type expression
 = Application of (expression * expression)
 | Identifier of string
 | Match of (expression * (pattern * expression) list)
type equality
 = Equality of (expression * expression)

type hint
  = Axiom
  | Induction of string
 
type declaration
   = TypeDeclaration of (string * typevariant list)
   | FunctionDeclaration of (typedVariable * typedVariable list * expression)
   | ProofDeclaration of (string * typedVariable list * equality * hint option)
 
let rec pattern_variables (pattern : pattern) : string list=
   match pattern with
   | Constructor (_, patterns) ->
       List.fold_left (fun acc pattern ->
           pattern_variables pattern @ acc) [] patterns
   | Variable (id, _) -> [id]

