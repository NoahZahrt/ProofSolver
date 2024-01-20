include Ast

module Parser = Parser
module Lexer = Lexer
exception Fail

let parse (s : string) : expression =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.expression_eof Lexer.token lexbuf in
     ast

let string_of_declaration = String_of.string_of_declaration

let empty = []
let singleton x y = [(x,y)]

let merge s1 s2 =
  let rec merge_helper s1 s2 =
    match s1, s2 with
    | [], _ -> Some s2 (* If s1 is empty, return s2 *)
    | (k1, v1) :: tl1, _ ->
        if List.exists (fun (k2, _) -> k1 = k2) s2 then None (* Same keys were found, return None which means merge failure *)
        else match merge_helper tl1 s2 with
          | Some merged -> Some ((k1, v1) :: merged) (* Add key value pair to result of the merge *)
          | None -> None
  in
  match merge_helper s1 s2 with
  | Some merged -> Some merged
  | None -> (* Check if s1 is empty *)
      if s1 = [] then Some s2
      else None (* failure due to a conflict *)


let rec check_list variables x = 
  match variables with 
    |[] -> false
    |TypedVariable(x1,_)::_ when x1 = x -> true
    |TypedVariable(_,x2)::_ when x2 = x -> true
    |TypedVariable(_,_)::tl -> check_list tl x 


let rec match_expression variables pattern expression =
  match pattern with
    | Identifier x -> if check_list variables x then (* Todo: fix test for variables: the string "x" is not necessarily the only variable and it might not always be a variable either *)
        (* if x is a variable: *)
        Some (singleton x expression)
        else
        (* if x is a constant: *)
        (if pattern = expression then Some empty else None)
    | Application (p1, p2) -> (* x has to be an application too, otherwise return None *)
        (match expression with
            | Application (e1, e2) ->
                (* We recursively match the sub-expressions.
                    This part is much easier to write if e2 is an expression (and it is for this particular ast),
                    because it's so symmetrical *)
                (match match_expression variables p1 e1, match_expression variables p2 e2 with
                | Some s1, Some s2 -> merge s2 s1
                | _ -> None)
            | _ -> None)
    | _ -> None


let rec find x s = match s with
  | [] -> failwith "Not found (find was passed an empty list)"
  | [(k,v)] -> if x = k then v else failwith "Not found (find failed but the substitution being passed in really does not contain the variable)"
  | (h1,h2)::tl -> if x = h1 then h2 else find x tl
  

let rec substitute variables s e = match e with
    | Identifier x -> if check_list variables x then find x s else e
    | Application (e1, e2) -> Application (substitute variables s e1, substitute variables s e2)
    | _ -> e

let rec attempt_rewrite variables lhs rhs expression =
  match match_expression variables lhs expression with
    | Some s -> Some (substitute variables s rhs)
    | None -> 
      (match expression with
      | Application (e1, e2) -> 
        (match attempt_rewrite variables lhs rhs e2 with
        | Some e2' -> Some (Application (e1, e2'))
        | None -> 
          (match attempt_rewrite variables lhs rhs e1 with 
          |Some e1' -> Some (Application(e1', e2))
          |None -> None) (* todo: try the other side too! *)
            )
        | _ -> None (* not succesful *)
        )

let rec perform_step rules expression = match rules with
  | (variables, nm, lhs, rhs):: rest -> (match attempt_rewrite variables lhs rhs expression with
      | Some e -> Some (nm, e)
      | _ -> perform_step rest expression)
  | _-> None 

let rec perform_steps rules expression = match perform_step rules expression with
  | Some (nm, e) -> (nm, e) :: perform_steps rules e
  | None -> []
  
  let rec prove rules lhs rhs
  = String_of.string_of_expression lhs :: 
    (match perform_steps rules lhs with
     | (nm, e) :: _ -> (" = { " ^ nm ^ " }") :: prove rules e rhs
     | [] -> if lhs = rhs then [] else " = { ??? }" :: [String_of.string_of_expression rhs])
  
     
     let rec prover rules declarations =
      match declarations with
         | ProofDeclaration (nm, vars, Equality (lhs,rhs), None) :: rest
            -> (* no hint, so let's prove this *)
               prove rules lhs rhs :: prover ((vars,nm,lhs,rhs)::rules) rest
         | ProofDeclaration (nm, vars, Equality (lhs,rhs), _) :: rest
            -> (* we got a hint so we simply assume the statement *)
               prover ((vars,nm,lhs,rhs)::rules) rest
         | _ :: rest -> prover rules rest
         | [] -> []
        
   let prover_main decls =
      prover [] decls |>
      List.map (String.concat "\n") |>
      String.concat "\n\n" |>
      print_endline
