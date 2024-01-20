{
 open Parser
 exception SyntaxError of string
}

let newline = '\r' | '\n' | "\r\n"

rule token = parse
 | [' ' '\t'] { token lexbuf }
 | newline { Lexing.new_line lexbuf; token lexbuf }
 | "(*prove*)" { PROVE }
 | "(*hint" { HINT }
 | "(*" { comment 0 lexbuf }
 | "*)" { ENDCOMMENT }
 | "*" { STAR }
 | "->" { ARROW }
 | "=" { EQUAL }
 | "," { COMMA }
 | ":" { COLON }
 | "|" { BAR }
 | "(" { LPAREN }
 | ")" { RPAREN }
 | ['a'-'z' 'A'-'Z' '0'-'9' '?' '_' '\'']+ as id { 
    match id with
    | "let" -> LET
    | "with" -> WITH
    | "match" -> MATCH
    | "of" -> OF
    | "type" -> TYPE
    | "rec" -> REC
    | "axiom" -> AXIOM
    | "induction" -> INDUCTION
    | _ -> IDENT id }
 | _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
 | eof { EOF }

and comment level = parse
 | "*)" { if level = 0 then token lexbuf else comment (level - 1) lexbuf }
 | newline { Lexing.new_line lexbuf; comment level lexbuf }
 | "(*" { comment (level + 1) lexbuf }
 | _ { comment level lexbuf }
 | eof { raise (SyntaxError "Unclosed comment") }

