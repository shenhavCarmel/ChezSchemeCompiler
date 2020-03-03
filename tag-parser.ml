#use "reader.ml";;
open Reader;;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct







(* work on the tag parser starts here *)                                       

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

let rec tag_parse readerOutput = match readerOutput with 
  | Bool(x) -> Const(Sexpr(Bool(x)))
  | Char(x) -> Const(Sexpr(Char(x)))
  | Number(x) -> Const(Sexpr(Number(x)))
  | String(x) -> Const(Sexpr(String(x)))
  | Symbol(x) -> if check_if_valid x 
                    then Var(x)
                    else raise X_syntax_error
  | Pair(Symbol("quote"), Pair(x, Nil)) -> Const(Sexpr(x))
  | TagRef(x) -> Const(Sexpr (TagRef (x)))
  | TaggedSexpr (x, Pair (Symbol "quote", Pair (value, Nil))) -> Const(Sexpr(TaggedSexpr(x, value)))
  (* | TaggedSexpr (x, Pair(value, Nil)) -> Const(Sexpr (TaggedSexpr(x, value))) *)
  | TaggedSexpr (x, value) -> Const(Sexpr (TaggedSexpr(x, value)))
  | Pair(Symbol("if"), Pair(test, Pair(dit, Nil))) -> If(tag_parse test, tag_parse dit, Const(Void))
  | Pair(Symbol( "if"), Pair(test, Pair(dit, Pair(dif, Nil)))) -> If(tag_parse test, tag_parse dit, tag_parse dif)
  | Pair(Symbol("lambda"), Pair(Symbol(x),body)) -> create_lambda_variadic x body
  | Pair(Symbol("lambda"), Pair(varsList, body)) -> create_lambda varsList body
  | Pair(Symbol("or"), Nil) -> Const(Sexpr(Bool(false)))
  | Pair(Symbol("or"), Pair(exp, Nil)) -> tag_parse exp
  | Pair(Symbol("or"), sexps) -> Or(List.rev (List.map tag_parse (pairs_to_list sexps []))) 
  | Pair(Symbol("set!"), Pair(var, Pair(value, Nil))) -> Set(tag_parse var, tag_parse value) 
  | Pair(Symbol("begin"), Nil) -> Const(Void)
  | Pair(Symbol("begin"), Pair(x, Nil)) -> tag_parse x
  | Pair(Symbol("begin"), x) -> Seq(List.rev (List.map tag_parse (pairs_to_list x [])))
  | Pair(Symbol("define"),Pair(name, Nil)) -> Def(tag_parse name, Const(Void))
  | Pair(Symbol("define"), Pair(Pair(name, arg), body)) -> create_define_mit name arg body
  | Pair(Symbol("define"), Pair(name, Pair(value, Nil))) -> Def(tag_parse name, tag_parse value)
  | Pair(Symbol("quasiquote"), Pair(x, Nil)) -> (tag_parse (create_qq x))
  | Pair(Symbol("cond"), ribs) -> create_cond ribs
  | Pair(Symbol("let"), Pair(ribs, body)) -> create_let ribs body
  | Pair(Symbol("let*"), Pair(ribs, body)) -> create_let_star ribs body
  | Pair(Symbol("letrec"), Pair(ribs, body)) -> create_let_rec ribs body
  | Pair(Symbol("and"),Nil) -> Const(Sexpr(Bool(true)))
  | Pair(Symbol("and"), rest) -> create_and rest
  | Pair(x,y) -> create_applic x y 
  |_ -> raise X_this_should_not_happen


(*------------------------------Helpful functions------------------------------------*)

and check_if_valid var = 
  if (List.mem var reserved_word_list)
    then false
    else true

and pairs_to_list pairsList currlist = match pairsList with
  | Pair(x, Nil) -> x::currlist
  | Pair(x,y) -> let newList = x::currlist in 
                  pairs_to_list y newList
  | _ -> raise X_syntax_error

and dotted_pairs_to_list dottedPairs currList = match dottedPairs with 
  | Pair (x, Pair(y, z)) -> let newList = x::currList in 
                            dotted_pairs_to_list (Pair(y, z)) newList
  | Pair (x, y) -> y::x::currList
  | _ -> raise X_syntax_error

and check_last_element pairsList = match pairsList with 
  | Pair(x, Nil) -> "simple"
  | Pair(x, Pair(y, z)) -> check_last_element (Pair(y,z))
  | Pair(x, y) -> "dotted"
  | _ -> raise X_syntax_error

and arg_to_var arg =  match arg with 
  | Symbol(x) -> if check_if_valid x 
                    then x
                    else raise X_syntax_error
  | _ -> raise X_syntax_error

and dup_args_checker args = 
  match args with
  |[] -> false
  |first::rest -> ((List.exists ((=) first) rest) || dup_args_checker rest)
(*------------------------------Lambdas------------------------------------*)

and create_lambda varList body = 
  if (varList = Nil) 
    then (match body with
          | Pair(exp, Nil) -> LambdaSimple ([], tag_parse exp) 
          | _ -> LambdaSimple([],Seq(List.rev(List.map tag_parse (pairs_to_list body [])))))
    else (let ans = check_last_element varList in 
          match ans with 
          | "simple" -> (let argsList = List.rev (List.map arg_to_var (pairs_to_list varList [])) in 
                          if(dup_args_checker argsList)
                            then raise X_syntax_error
                            else (match body with
                                  | Pair(exp, Nil) -> LambdaSimple(argsList, tag_parse exp)
                                  | _ -> LambdaSimple(argsList, Seq(List.rev (List.map tag_parse (pairs_to_list body []))))))
          | "dotted" -> let argList = (List.rev (List.map arg_to_var (dotted_pairs_to_list varList []))) in
                        let revFirst = List.tl (List.rev argList) in
                        let revBack = List.rev revFirst in
                        if(dup_args_checker revBack)
                          then raise X_syntax_error
                          else (match body with 
                                | Pair(exp, Nil) -> LambdaOpt(revBack, List.nth argList ((List.length argList) - 1) ,tag_parse exp)  
                                | _ -> LambdaOpt(revBack, List.nth argList ((List.length argList) - 1) ,Seq(List.rev(List.map tag_parse (pairs_to_list body [])))))
          | _ -> raise X_syntax_error)

                
and create_lambda_variadic arg body = 
  match body with
  | Pair(exp, Nil) -> LambdaOpt([], arg,tag_parse exp)
  | _ -> LambdaOpt([], arg,Seq(List.rev(List.map tag_parse (pairs_to_list body []))))

(*------------------------------Applic------------------------------------*)


and create_applic operator operands = 
  if (operands = Nil)
   then Applic(tag_parse operator, [])
   else Applic (tag_parse operator,List.rev (List.map tag_parse (pairs_to_list operands []))) 

(*-------------------------Quazi-Quote--------------------------------- *)

and create_qq qqSexp = 
  match qqSexp with
  | Pair(Symbol("unquote"), Pair(x, Nil)) -> x
  | Pair(Symbol("unquote-splicing"), Pair(x, Nil)) -> raise X_syntax_error
  | Pair(x, y) -> (match x,y with
                  | Pair(Symbol("unquote-splicing"), Pair(z, Nil)), _ -> Pair(Symbol("append"),Pair(z , Pair((create_qq y),Nil)))
                  | _ , Pair(Symbol("unquote-splicing"), Pair(z, Nil)) -> Pair(Symbol("cons"), Pair((create_qq x), Pair(z, Nil)))
                  |_ -> Pair(Symbol("cons") , Pair((create_qq x),Pair((create_qq y) , Nil))))
  | Nil -> Pair(Symbol("quote") , Pair(qqSexp, Nil))
  | Symbol(x) -> Pair(Symbol("quote") , Pair(qqSexp, Nil))               
  |_ -> qqSexp    


(*------------------------------Cond------------------------------------*)

and create_cond ribs =
  match ribs with
  |Pair(rib, Nil) -> (match rib with
                  |Pair(Symbol("else"), rest) -> (match rest with
                                                 | Pair(exp, Nil) -> tag_parse exp
                                                 | _ -> Seq(List.rev (List.map tag_parse (pairs_to_list rest []))))
                  |Pair(test, Pair(Symbol("=>"), Pair(app, Nil))) -> Applic(LambdaSimple(["value"; "f"], If(Var("value"),Applic(Applic(Var("f"), []),[Var("value")]), Const(Void))), [tag_parse test; LambdaSimple([],tag_parse app)])                  
                  |Pair(test, rest) -> (match rest with
                                        | Nil -> If((tag_parse test) , Const(Void), Const(Void)) 
                                        | Pair(exp, Nil) -> If((tag_parse test), tag_parse exp, Const(Void)) 
                                        | _ -> If((tag_parse test), Seq(List.rev (List.map tag_parse (pairs_to_list rest []))), Const(Void)))
                  |_ -> raise X_syntax_error)
  |Pair(rib, rest) -> (match rib with
                    |Pair(Symbol("else"), rest1) -> (match rest1 with
                                                   | Nil -> Const(Void)
                                                   | Pair(exp, Nil) -> tag_parse exp
                                                   | _ -> Seq(List.rev (List.map tag_parse (pairs_to_list rest1 []))))
                    |Pair(test, Pair(Symbol("=>"), Pair(app, Nil))) -> Applic(LambdaSimple(["value"; "f"; "rest"], If(Var("value"),Applic(Applic(Var("f"), []),[Var("value")]), Applic(Var("rest"), []))), [tag_parse test; LambdaSimple([], tag_parse app);LambdaSimple([], create_cond rest )])
                    |Pair(test, dit) -> (match dit with
                                        | Nil -> Const(Void)
                                        | Pair(exp, Nil) -> If((tag_parse test), tag_parse exp, create_cond rest)
                                        | _ -> If((tag_parse test), Seq(List.rev (List.map tag_parse (pairs_to_list dit []))), create_cond rest)) 
                    |_ -> raise X_syntax_error)
  |_ -> raise X_syntax_error 



(*------------------------------Let------------------------------------*)

and get_ribs_vars ribs currList = 
  match ribs with
  |Pair(Pair(x,Pair(y, Nil)), Nil) -> x::currList
  |Pair(Pair(x,Pair(y, Nil)), rest) -> get_ribs_vars rest (x::currList) 
  |_ -> raise X_syntax_error

and get_ribs_vals ribs currList = 
  match ribs with
  |Pair(Pair(x,Pair(y,Nil)),Nil) -> y::currList
  |Pair(Pair(x,Pair(y,Nil)), rest) -> get_ribs_vals rest (y::currList) 
  |_ -> raise X_syntax_error  


and create_let ribs body = 
  (let parsed_body = (match body with
                      | Pair(exp, Nil) -> tag_parse exp
                      | _ -> Seq(List.rev (List.map tag_parse (pairs_to_list body [])))) in
  if(ribs = Nil)
    then Applic(LambdaSimple([],parsed_body),[]) 
    else (let vars = get_ribs_vars ribs [] in
          let vals = get_ribs_vals ribs [] in
          let parsedVars = List.rev (List.map arg_to_var vars) in
          let parsedVals = List.rev (List.map tag_parse vals) in
          if(dup_args_checker parsedVars)
            then raise X_syntax_error
            else Applic(LambdaSimple(parsedVars, parsed_body),parsedVals)
          )) 

(*------------------------------Let_star------------------------------------*)

and create_let_star ribs body =
  match ribs with
  | Nil -> let parsed_body = (match body with
                              | Pair(exp, Nil) -> tag_parse exp
                              | _ -> Seq(List.rev (List.map tag_parse (pairs_to_list body [])))) in
           Applic(LambdaSimple([],parsed_body),[]) 
  | Pair(Pair(x,Pair(y,Nil)),Nil) -> let parsed_body = (match body with
                                                        | Pair(exp, Nil) -> tag_parse exp
                                                        | _ -> Seq(List.rev (List.map tag_parse (pairs_to_list body [])))) in
                                     Applic(LambdaSimple([arg_to_var x], parsed_body),[tag_parse y])
                                     (*add before creat let star recursia seq????? *)
  | Pair(Pair(x,Pair(y,Nil)),rest) -> Applic(LambdaSimple([arg_to_var x], create_let_star rest body), [tag_parse y])
  | _ -> raise X_syntax_error 

(*------------------------------Let_rec------------------------------------*)
 
and make_set_list ribs currList=
  match ribs with
  |Pair(Pair(x,Pair(y,Nil)),Nil) -> (Set(tag_parse x, tag_parse y))::currList
  |Pair(Pair(x,Pair(y,Nil)),rest) -> make_set_list rest (Set(tag_parse x, tag_parse y)::currList)
  |_ -> raise X_syntax_error

and make_void_list ribs currList = 
  match ribs with
  |Pair(Pair(x,Pair(y,Nil)),Nil) -> (Const(Sexpr(Symbol("whatever"))))::currList
  |Pair(Pair(x,Pair(y,Nil)),rest) -> make_void_list rest (Const(Sexpr(Symbol("whatever")))::currList)
  |_ -> raise X_syntax_error 

and create_let_rec ribs body =
  let parsed_body = List.rev (List.map tag_parse (pairs_to_list body [])) in 
  if(ribs = Nil)
    then (match body with
          | Pair(x, Nil) -> Applic(LambdaSimple([],tag_parse x),[]) 
          | _ -> Applic(LambdaSimple([],Seq(parsed_body)),[]))
    else (let setList = make_set_list ribs [] in
          let subLetBody = parsed_body in
          let mainLetBody = Seq(List.rev (List.append subLetBody setList)) in
          let vars = get_ribs_vars ribs [] in
          let mainLetVars = List.rev (List.map arg_to_var vars) in
          let mainLetVals = List.rev (make_void_list ribs []) in
          Applic(LambdaSimple(mainLetVars, mainLetBody),mainLetVals)
    )
(*-----------------------------and----------------------------------------*)
and create_and andList = 
  match andList with
  | Pair(x, Nil) -> tag_parse x
  | Pair(x, Pair(y, Nil)) -> If((tag_parse x), (tag_parse y), Const(Sexpr(Bool(false))))
  | Pair(x, rest) -> If((tag_parse x), create_and rest, Const(Sexpr(Bool(false))))
  |_ -> raise X_syntax_error

(*------------------------------Define-MIT----------------------------- *)
and create_define_mit name args body = 
  (match args with
          | Symbol(x) -> Def(tag_parse name,  (create_lambda_variadic x body))
          | _ -> Def(tag_parse name, (create_lambda args body)))
                       
;;
 

let tag_parse_expression sexpr =
  (tag_parse sexpr);;

let tag_parse_expressions sexpr = 
  (List.map tag_parse sexpr);;

end;; (* struct Tag_Parser *)  
