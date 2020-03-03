#use "reader.ml";;
open Reader;;
#use "tag-parser.ml";;
open Tag_Parser;;
open Format;;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct




(*--------------counter-----------------*)
let make_counter () =
let x = ref 0 in
let get () = !x in 
let inc () = x := !x + 1 in 
(get,inc);;

(* --------------------------First Step - tag vars type ---------------------------*)
let rec checkMinor var params index =
    match params with 
    | [] -> -1
    | p::[] -> (if (p = var)
                  then index
                  else -1)
    | p::rest -> (if (p = var)
                  then index
                  else checkMinor var rest (index+1));;


let rec boundCheck var env major = 
    match env with
    | [] -> Var'(VarFree(var))
    | e::[] -> (let minor = checkMinor var e 0 in 
                 if (minor = -1)
                  then Var'(VarFree(var))
                  else Var'(VarBound(var, major, minor)))
    | e::rest -> (let minor = checkMinor var e 0 in 
                 if (minor = -1)
                  then boundCheck var rest (major+1)
                  else Var'(VarBound(var, major, minor)));;
  
let rec convert_vars exp env params = 
  match exp with
  | Const(x) -> Const'(x)
  | Var(x) -> (let paramCheck = (checkMinor x params 0) in
               if (paramCheck != -1)
                then Var'(VarParam(x, paramCheck))
                else (boundCheck x env 0)) 
  | If(test, dit, dif) -> If'(convert_vars test env params, convert_vars dit env params, convert_vars dif env params)
  | Seq(expList) -> Seq'(List.map (fun exp -> (convert_vars exp env params)) expList)
  | Set(var, exp) -> Set'(convert_vars var env params, convert_vars exp env params)
  | Def(var, exp) -> Def'(convert_vars var env params, convert_vars exp env params)
  | Or(expList) -> Or'(List.map (fun exp -> (convert_vars exp env params)) expList)
  | LambdaSimple(arg, body) -> LambdaSimple'(arg, (convert_vars body (params::env) arg))
  | LambdaOpt(arg, optArg, body) -> LambdaOpt'(arg, optArg, (convert_vars body (params::env) (List.append arg [optArg])))
  | Applic(rator, rands) -> Applic'(convert_vars rator env params, List.map (fun exp -> (convert_vars exp env params)) rands);;


(* -------------------------- Second Step - tag tail calls ---------------------------*)
let last_element expList = 
  let reversed_list = List.rev expList in
  (List.hd reversed_list);;



let rec convert_tail_calls exp isTailCall = 
  match exp with
  | Set'(var, exp) -> Set'(var, convert_tail_calls exp false)                        
  | Def'(var, exp) -> Def'(var, convert_tail_calls exp false)
  | If'(test, dit, dif) -> (if(isTailCall)
                           then If'(convert_tail_calls test false, convert_tail_calls dit true, convert_tail_calls dif true)
                           else If'(convert_tail_calls test false, convert_tail_calls dit false, convert_tail_calls dif false))
  | Seq'(expList) -> (if(isTailCall)
                      then (let seq_last_element = last_element expList in
                            let unconverted_list = List.rev (List.tl (List.rev expList)) in
                            let converted_list = List.map (fun a -> (convert_tail_calls a false)) unconverted_list in  
                            let seq_last_element_TP = convert_tail_calls seq_last_element true in 
                            Seq'(List.rev (seq_last_element_TP::(List.rev converted_list))))
                      else Seq'(List.map (fun a -> (convert_tail_calls a false)) expList))
  | Or'(expList) -> (if(isTailCall)
                     then (let or_last_element = last_element expList in
                           let unconverted_list = List.rev (List.tl (List.rev expList)) in 
                           let converted_list = List.map (fun a -> (convert_tail_calls a false)) unconverted_list in
                           let or_last_element_TP = convert_tail_calls or_last_element true in 
                           Or'(List.rev (or_last_element_TP::(List.rev converted_list))))
                     else Or'(List.map (fun a -> (convert_tail_calls a false)) expList))
                    
  | LambdaSimple'(arg, body) -> LambdaSimple'(arg, convert_tail_calls body true)                   
  | LambdaOpt' (arg, optArg, body) -> LambdaOpt' (arg, optArg, convert_tail_calls body true)                                       
  | Applic'(rator, rands) -> (if(isTailCall)
                              then ApplicTP'(convert_tail_calls rator false, List.map (fun a -> convert_tail_calls a false) rands) 
                              else Applic'(convert_tail_calls rator false, List.map (fun a -> convert_tail_calls a false) rands))
  | _ -> exp;;                                                                                 

(* --------------------------Third Step - tag boxed vars ---------------------------*)

let rec have_read exp var numOfLambdaRef firstScope = 
  match exp with
  | Var'(VarBound(x ,y, z)) -> (if (x = var) 
                                then (if firstScope 
                                      then [0] 
                                      else [(fst numOfLambdaRef)()])
                                else [])
  | Var'(VarParam(x ,y)) -> (if (x = var) 
                             then (if firstScope 
                                   then [0] 
                                   else [(fst numOfLambdaRef)()])
                             else [])       
  | If'(test, dit, dif) -> (let a = have_read test var numOfLambdaRef firstScope in
                            let b = List.append a (have_read dit var numOfLambdaRef firstScope) in
                            List.append b (have_read dif var numOfLambdaRef firstScope))
  | Set'(x, y) -> have_read y var numOfLambdaRef firstScope
  | Def'(x, y) -> have_read y var numOfLambdaRef firstScope
  | Seq'(expList) ->(let a = List.map (fun a -> have_read a var numOfLambdaRef firstScope) expList in
                    (List.fold_left (fun acc curr -> List.append acc curr) [] a))
  | Or'(expList) -> (let a = List.map (fun a -> have_read a var numOfLambdaRef firstScope) expList in
                    (List.fold_left (fun acc curr -> List.append acc curr) [] a))
  | Applic'(rator, rands) -> (let a = have_read rator var numOfLambdaRef firstScope in
                             let b = List.map (fun a -> have_read a var numOfLambdaRef firstScope) rands in
                             let c = (List.fold_left (fun acc curr -> List.append acc curr) [] b) in
                             List.append a c)
  | ApplicTP'(rator, rands) -> (let a = have_read rator var numOfLambdaRef firstScope in
                             let b = List.map (fun a -> have_read a var numOfLambdaRef firstScope) rands in
                             let c = (List.fold_left (fun acc curr -> List.append acc curr) [] b) in
                             List.append a c)
  | LambdaSimple'(args, body) -> (if(List.mem var args)
                                  then []
                                  else (if firstScope
                                        then (let () = (snd numOfLambdaRef()) in 
                                              have_read body var numOfLambdaRef false)
                                        else have_read body var numOfLambdaRef firstScope))
  | LambdaOpt'(args, optArg, body) -> (if(List.mem var (optArg::args))
                                       then []
                                       else (if firstScope
                                             then (let () = (snd numOfLambdaRef)() in 
                                                    have_read body var numOfLambdaRef false)
                                             else have_read body var numOfLambdaRef firstScope))
  | _ -> [] ;;


let rec have_write exp var numOfLambdaRef firstScope =   
  match exp with
  | If'(test, dit, dif) -> (let a = have_write test var numOfLambdaRef firstScope in
                            let b = List.append a (have_write dit var numOfLambdaRef firstScope) in
                            List.append b (have_write dif var numOfLambdaRef firstScope))
  | Set'(Var'(VarParam(x, y)), z) -> (if(x = var)
                                     then (if firstScope 
                                           then (List.append [0] (have_write z var numOfLambdaRef firstScope))
                                           else List.append [(fst numOfLambdaRef)()] (have_write z var numOfLambdaRef firstScope))
                                     else (have_write z var numOfLambdaRef firstScope))
  | Set'(Var'(VarBound(x, y, z)), w) -> (if(x = var)
                                         then (if firstScope 
                                               then (List.append [0] (have_write w var numOfLambdaRef firstScope)) 
                                               else List.append [(fst numOfLambdaRef)()] (have_write w var numOfLambdaRef firstScope))
                                         else (have_write w var numOfLambdaRef firstScope))
  | Set'(x, y) -> have_write y var numOfLambdaRef firstScope
  | Def'(x, y) -> have_write y var numOfLambdaRef firstScope
  | Seq'(expList) ->(let a = List.map (fun a -> have_write a var numOfLambdaRef firstScope) expList in
                    (List.fold_left (fun acc curr -> List.append acc curr) [] a))
  | Or'(expList) -> (let a = List.map (fun a -> have_write a var numOfLambdaRef firstScope) expList in
                    (List.fold_left (fun acc curr -> List.append acc curr) [] a))
  | Applic'(rator, rands) -> (let a = have_write rator var numOfLambdaRef firstScope in
                             let b = List.map (fun a -> have_write a var numOfLambdaRef firstScope) rands in
                             let c = (List.fold_left (fun acc curr -> List.append acc curr) [] b) in
                             List.append a c)
  | ApplicTP'(rator, rands) -> (let a = have_write rator var numOfLambdaRef firstScope in
                               let b = List.map (fun a -> have_write a var numOfLambdaRef firstScope) rands in
                               let c = (List.fold_left (fun acc curr -> List.append acc curr) [] b) in
                               List.append a c)                             
  | LambdaSimple'(args, body) -> (if(List.mem var args)
                                  then []
                                  else (if firstScope
                                        then (let () = (snd numOfLambdaRef()) in 
                                              have_write body var numOfLambdaRef false)
                                        else have_write body var numOfLambdaRef firstScope))
  | LambdaOpt'(args, optArg, body) -> (if(List.mem var (optArg::args))
                                       then []
                                       else (if firstScope
                                             then (let () = (snd numOfLambdaRef)() in 
                                                    have_write body var numOfLambdaRef false)
                                             else have_write body var numOfLambdaRef firstScope))
  | _ -> [] ;;


let rec second_check scopeToCheck l2 = (match l2 with
                                        | [] -> false
                                        | last::[] -> (scopeToCheck != last)
                                        | first::rest -> (if(scopeToCheck = first)
                                                          then (second_check scopeToCheck rest)
                                                          else true)
                            );; 


let rec first_check l1 l2 = (match l1 with
                            | [] -> false
                            | last::[] -> (second_check last l2)
                            | first::rest -> (if(second_check first l2)
                                              then true
                                              else (first_check rest l2))
                            );;



let should_box exp var =
  let numOfLambdasRef1 = make_counter() in
  let numOfLambdasRef2 = make_counter() in
  let read_list = have_read exp var numOfLambdasRef1 true in
  let write_list = have_write exp var numOfLambdasRef2 true in
  (first_check read_list write_list);; 


let rec box_body body arg = 
  match body with
    | Var'(VarParam(x, y)) -> if (x = arg) 
                              then BoxGet'(VarParam(x, y))
                              else body
    | Var'(VarBound(x, y, z)) -> if (x = arg) 
                                 then  BoxGet'(VarBound(x, y, z))
                                 else body             
    | Set'(Var'(VarParam(x, y)),z) -> if (x = arg)
                                      then BoxSet'(VarParam(x, y), box_body z arg)
                                      else Set'(Var'(VarParam(x, y)), box_body z arg) 
    | Set'(Var'(VarBound(x, y, z)), w) -> if (x = arg)
                                          then BoxSet'(VarBound(x, y, z), box_body w arg)
                                          else Set'(Var'(VarBound(x, y, z)), box_body w arg)
    | BoxSet'(x, y) -> BoxSet'(x, box_body y arg)
    | Set'(x, y) -> Set'(x, box_body y arg)
    | If'(test, dit, dif) -> If'(box_body test arg, box_body dit arg, box_body dif arg)
    | Def'(x, y) -> Def'(x, box_body y arg)
    | Or'(expList) -> Or'(List.map (fun a -> box_body a arg) expList)
    | Seq'(expList) -> Seq'(List.map (fun a -> box_body a arg) expList)
    | Applic'(rator, rands) -> Applic'(box_body rator arg, List.map (fun a -> box_body a arg) rands)
    | ApplicTP'(rator, rands) -> ApplicTP'(box_body rator arg, List.map (fun a -> box_body a arg) rands)
    | LambdaSimple'(args, body) -> if (List.mem arg args) 
                                    then LambdaSimple'(args, body)
                                    else LambdaSimple'(args, box_body body arg)
    | LambdaOpt'(args, optArg, body) -> if (arg = optArg)
                                          then LambdaOpt'(args, optArg, body)
                                          else LambdaOpt'(args, optArg, box_body body arg)
    | _ -> body
;;


let rec create_set_exps boxed_args args = 
  match boxed_args with
  | [] -> []
  | last::[] -> ([Set'(Var'(VarParam(last, (checkMinor last args 0))), Box'(VarParam(last, (checkMinor last args 0))))])
  | curr::restArgs -> ((Set'(Var'(VarParam(curr, (checkMinor curr args 0))), Box'(VarParam(curr, (checkMinor curr args 0)))))::(create_set_exps restArgs args));;


let rec convert_box exp = 
  match exp with 
  | If'(test, dit, dif) -> If'(convert_box test, convert_box dit, convert_box dif)
  | Set'(x, y) -> Set'(x, convert_box y)
  | Def'(x, y) -> Def'(x, convert_box y)
  | Or'(expList) -> Or'(List.map convert_box expList)
  | Seq'(expList) -> Seq'(List.map convert_box expList)
  | Applic'(rator, rands) -> Applic'(convert_box rator, List.map convert_box rands)
  | ApplicTP'(rator, rands) -> ApplicTP'(convert_box rator, List.map convert_box rands)
  | LambdaSimple'(args, body) -> (let boxed_args = List.filter (fun a -> should_box body a) args in
                                  if(boxed_args = [])
                                  then LambdaSimple'(args, convert_box body)
                                  else (let boxed_addition = create_set_exps boxed_args args in
                                        let boxed_body = List.fold_right (fun curr acc -> box_body acc curr) boxed_args body in
                                        LambdaSimple'(args, convert_box (Seq'(List.append boxed_addition [boxed_body])))))
  | LambdaOpt'(args, optArg, body) -> (let boxed_args = List.filter (fun a -> should_box body a) (List.append args [optArg]) in
                                       if(boxed_args = [])
                                       then LambdaOpt'(args, optArg, convert_box body)
                                       else (let boxed_addition = create_set_exps boxed_args (List.append args [optArg]) in
                                             let boxed_body = List.fold_right (fun curr acc -> box_body acc curr) boxed_args body in
                                             LambdaOpt'(args, optArg, convert_box (Seq'(List.append boxed_addition [boxed_body])))))
                                                                          
  | _ -> exp
;;                               

  let annotate_lexical_addresses e = (convert_vars e [] []);; 

let annotate_tail_calls e = (convert_tail_calls e false);;

let box_set e = (convert_box e)

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; (* struct Semantics *)
