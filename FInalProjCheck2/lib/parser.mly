%{
  open Ast
%}
%token <string> IDENT
%token COLON
%token LPAREN
%token RPAREN
%token PROVE
%token LET
%token REC
%token EQUAL
%token MATCH
%token WITH
%token BAR
%token ARROW
%token OF
%token STAR
%token EOF
%token HINT
%token TYPE
%token COMMA
%token INDUCTION
%token ENDCOMMENT /* there is no startcomment, as it's called "hint", and proper comments are ignored by the lexer */
%token AXIOM
%start main
%start expression_eof
%type <expression> expression_eof
%type <declaration list> main
%%

main:
| list(declaration) EOF { $1 }
declaration:
| LET ; PROVE ; lemma_name=IDENT ; args = list(argument) ; EQUAL ; eq = equality ; hint=option(hint)
   { ProofDeclaration (lemma_name, args, eq, hint) }
| LET ; REC ; nm = IDENT ; args = list(argument) ; COLON ; t = IDENT ; EQUAL ; e = expression_or_match { FunctionDeclaration (TypedVariable (nm,t), args, e) }
| TYPE ; nm = IDENT ; EQUAL ; option(BAR); t = separated_nonempty_list(BAR,variant)  { TypeDeclaration (nm, t) }
argument:
| nm = IDENT; COLON; t = IDENT { TypedVariable (nm, t) }
| LPAREN ; arg = argument; RPAREN { arg }
equality:
| LPAREN ; e = equality ; RPAREN { e }
| lhs = expression ; EQUAL ; rhs = expression { Equality (lhs, rhs) }
// some groups have been writing (*hint : axiom *) instead of (*hint: axiom *)
// I decided I should just allow that so this parser parses the colon separately now:
hint:
| HINT ; COLON; AXIOM ; ENDCOMMENT { Axiom }
| HINT ; COLON; INDUCTION ; nm = IDENT ; ENDCOMMENT { Induction nm }
expression:
| LPAREN ; e = expression_with_commas ; RPAREN { e }
| lhs = expression ; arg = IDENT { Application (lhs, Identifier arg) }
| lhs = expression ; LPAREN ; arg = expression_with_commas ; RPAREN
   { Application (lhs, arg) }
| nm = IDENT { Identifier nm }

// for expression_with_commas, we're using that "," is not a valid identifier
// We're using it as an identifier that stands for the function (fun x y -> (x, y))
// This also means we're representing (x,y,z) and ((x,y),z) as the same thing.
expression_with_commas:
| e = expression { e }
| e1 = expression_with_commas ; COMMA ; e2 = expression
  { Application (Application (Identifier ",", e1), e2)}

// this is for the type declarations, which are like: type t = A | B of (int * int)
variant:
| nm = IDENT { Variant(nm,[]) }
| nm = IDENT; OF; LPAREN ; args = separated_nonempty_list(STAR, IDENT); RPAREN { Variant(nm,args) }
// the version without the parentheses isn't really used, but it's allowed
| nm = IDENT; OF ; args = separated_nonempty_list(STAR, IDENT) { Variant(nm,args) }

expression_eof:
| e = expression_or_match ; EOF {e}
expression_or_match:
| e = expression { e }
| MATCH ; e = expression ; WITH ; option(BAR) ; cases = separated_nonempty_list(BAR,case) { Match (e, cases) }
case:
| pattern = pattern ; ARROW ; expr = expression { (pattern, expr) }
pattern:
| LPAREN ; p = pattern ; RPAREN { p }
| nm = IDENT { Constructor (nm, []) }
| nm = IDENT ; LPAREN ; args = separated_list(COMMA,pattern) ; RPAREN { Constructor (nm, args) }
| nm = IDENT ; COLON ; t = IDENT { Variable (nm,t) }
