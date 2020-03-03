#use "reader.ml";;
open Reader;;
#use "tag-parser.ml";;
open Tag_Parser;;
#use "semantic-analyser.ml";;
open Semantics;;

open Printf;;
(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "SOB_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* This signature represents the idea of outputing assembly code as a string
     for a single AST', given the full constants and fvars tables. 
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct


(* let make_consts_tbl asts = raise X_not_yet_implemented;;

let make_fvars_tbl asts = raise X_not_yet_implemented;; 

let generate consts fvars e = "";;


end;; *)


(*------------------------------Helpfull Functions-------------------------------*)
  let make_counter () =
  let x = ref 0 in
  let get () = !x in 
  let inc () = x := !x + 1 in 
  (get,inc);;
  let global_counter = make_counter();;
  let rec remove_dup list1 list2 = 
    match list1 with
    | [] -> list2
    | name::rest -> (if (List.mem name list2)
                     then remove_dup rest list2
                     else remove_dup rest (name::list2));;

(*---------------------------Handle Tagged Exp-----------------------*)
let add_counter name counter = 
  Printf.sprintf "%s%d" name ((fst counter)());;

let rec rename_sexp expr counter = 
  match expr with
  | TaggedSexpr(name, value) -> TaggedSexpr(add_counter name counter, rename_sexp value counter)
  | TagRef(x) -> TagRef(add_counter x counter)
  | Pair(x, y) -> Pair(rename_sexp x counter, rename_sexp y counter)
  |_ -> expr;;


let rec rename expr counter = 
  match expr with
  | Const'(Sexpr(TaggedSexpr(x, sexp))) -> Const'(Sexpr(TaggedSexpr(add_counter x counter, (rename_sexp sexp counter))))
  | Const'(Sexpr(TagRef(x))) -> Const'(Sexpr(TagRef(add_counter x counter)))
  | BoxSet'(var, value) -> BoxSet'(var, rename value counter)
  | If'(test, dit, dif) -> If'(rename test counter, rename dit counter, rename dif counter)
  | Seq'(expList) -> Seq'(List.map (fun a -> rename a counter) expList)
  | Set'(var, value) -> Set'(var, rename value counter)
  | Def'(var, value) -> Def'(var, rename value counter)
  | Or'(expList) -> Or'(List.map (fun a -> rename a counter) expList)
  | LambdaSimple'(args, body) -> LambdaSimple'(args, rename body counter)
  | LambdaOpt'(args, optArg, body) -> LambdaOpt'(args, optArg, rename body counter)
  | Applic'(rator, rands)-> Applic'(rename rator counter, List.map (fun a -> rename a counter) rands)
  | ApplicTP'(rator, rands)-> ApplicTP'(rename rator counter, List.map (fun a -> rename a counter) rands)
  | _ -> expr;;


let rename_tagged_sexp asts = 
  let counter = make_counter() in
  let func curr acc = (let _ = (snd counter)() in
                        let new_curr = rename curr counter in
                        (new_curr::acc)) in
  List.rev (List.fold_right func asts []);;

let rec get_tagged_collection_sexp expr collection = 
  match expr with
  | TaggedSexpr(name, value) -> get_tagged_collection_sexp value (TaggedSexpr(name, value)::collection)
  | Pair(x, y) -> List.append collection (List.append (get_tagged_collection_sexp x []) (get_tagged_collection_sexp y []))
  |_ -> collection;;

let rec get_tagged_collection expr collection = 
  match expr with 
  | Const'(Sexpr(TaggedSexpr(x, y))) -> get_tagged_collection_sexp y (TaggedSexpr(x, y)::collection)  
  | BoxSet'(var, exp) -> get_tagged_collection exp collection 
  | If'(test, dit, dif) -> (let a = List.append (get_tagged_collection test []) (get_tagged_collection dit []) in
                            List.append a (get_tagged_collection dif collection))
  | Seq'(exprs) -> (let const_per_seq acc curr = List.append acc (get_tagged_collection curr []) in
                      List.fold_left const_per_seq collection exprs)
  | Set'(var, value) -> get_tagged_collection value collection
  | Def'(var, value) -> get_tagged_collection value collection
  | Or'(exprs) -> (let const_per_or acc curr = List.append acc (get_tagged_collection curr []) in
                   List.fold_left const_per_or collection exprs)
  | LambdaSimple'(args, body) -> get_tagged_collection body collection
  | LambdaOpt'(args, optArg, body) -> get_tagged_collection body collection
  | Applic'(rator, rands) -> (let const_per_rand acc curr = List.append acc (get_tagged_collection curr []) in
                              let rands_const_names = List.fold_left const_per_rand [] rands in
                              List.append (get_tagged_collection rator collection) rands_const_names)               
  | ApplicTP'(rator, rands) -> (let const_per_rand acc curr = List.append acc (get_tagged_collection curr []) in
                                let rands_const_names = List.fold_left const_per_rand [] rands in
                                List.append (get_tagged_collection rator collection) rands_const_names) 
  | _ -> collection;;  


(*-------------------------------Const Table----------------------------*)
 let rec get_consts_names expr name_list = 
    match expr with
    | Const'(x) -> x::name_list
    | BoxSet'(var, exp) -> get_consts_names exp name_list 
    | If'(test, dit, dif) -> (let a = List.append (get_consts_names test []) (get_consts_names dit []) in
                              List.append a (get_consts_names dif name_list))
    | Seq'(exprs) -> (let const_per_seq acc curr = List.append acc (get_consts_names curr []) in
                      List.fold_left const_per_seq name_list exprs)
    | Set'(var, value) -> get_consts_names value name_list
    | Def'(var, value) -> get_consts_names value name_list
    | Or'(exprs) -> (let const_per_or acc curr = List.append acc (get_consts_names curr []) in
                      List.fold_left const_per_or name_list exprs)
    | LambdaSimple'(args, body) -> get_consts_names body name_list
    | LambdaOpt'(args, optArg, body) -> get_consts_names body name_list
    | Applic'(rator, rands) -> (let const_per_rand acc curr = List.append acc (get_consts_names curr []) in
                                let rands_const_names = List.fold_left const_per_rand [] rands in
                                List.append (get_consts_names rator name_list) rands_const_names)               
    | ApplicTP'(rator, rands) -> (let const_per_rand acc curr = List.append acc (get_consts_names curr []) in
                            let rands_const_names = List.fold_left const_per_rand [] rands in
                            List.append (get_consts_names rator name_list) rands_const_names) 
    | _ -> name_list;;

let rec expand_sexp sexp expended_list = 
  match sexp with
  |Pair(x, y) -> List.append (expand_sexp x expended_list) (List.append (expand_sexp y []) [Sexpr(Pair(x, y))])
  |TaggedSexpr(name, value) -> expand_sexp value expended_list
  |_ -> List.append expended_list [Sexpr(sexp)];;



let rec expand_const_list const_list expanded_const_list = 
  match const_list with
  | [] -> expanded_const_list
  | Void::rest -> expand_const_list rest (List.append expanded_const_list [Void])
  | Sexpr(Symbol(x))::rest -> expand_const_list rest (List.append expanded_const_list [Sexpr(String(x)); Sexpr(Symbol(x))])
  | Sexpr(TaggedSexpr(name, value))::rest -> expand_const_list rest (List.append expanded_const_list (expand_sexp value []))
  | Sexpr(Pair(x, y))::rest -> (match x,y with
                                | TaggedSexpr(name1, sexp1), TaggedSexpr(name2, sexp2) -> expand_const_list (List.append [Sexpr(sexp1); Sexpr(sexp2)] rest) (List.append expanded_const_list [Sexpr(Pair(x, y))])
                                | TaggedSexpr(name1, sexp1), x -> (let a = List.append (expand_const_list [Sexpr(sexp1); Sexpr(x)] []) [Sexpr(Pair(x, y))] in
                                                                   expand_const_list rest (List.append expanded_const_list a))
                                | x, TaggedSexpr(name1, sexp1) -> (let a = List.append (expand_const_list [Sexpr(x); Sexpr(sexp1)] []) [Sexpr(Pair(x, y))] in
                                                                   expand_const_list rest (List.append expanded_const_list a))
                                | x, Nil -> let a = expand_const_list [Sexpr(x)] [] in
                                             expand_const_list rest (List.append expanded_const_list (List.append a [Sexpr(Pair(x, y))]))
                                | x, y -> expand_const_list rest (List.append expanded_const_list (List.append (expand_const_list [Sexpr(x); Sexpr(y)] []) [Sexpr(Pair(x, y))])))
  | c::rest -> expand_const_list rest (List.append expanded_const_list [c]);; 

let get_sexp_val sexp = 
  match sexp with
  | Sexpr(x) -> x 
  | _ -> raise X_this_should_not_happen;;

let check_equal sexp1 sexp2 =
  match sexp1, sexp2 with
  | Void, Void -> true
  | _, Void -> false
  | Void, _ -> false
  | sexp1,sexp2-> (sexpr_eq (get_sexp_val sexp1) (get_sexp_val sexp2));;

let rec findOffset const const_list =
  match const_list with 
  | [] -> -1
  | c::rest -> (match c with
                | (sexp, (offset, _)) -> if (check_equal sexp const)
                                           then offset
                                           else findOffset const rest);;



let rec getAssembly const prev_consts_list = 
  match const with
  | Void -> "MAKE_VOID"
  | Sexpr(Nil) -> "MAKE_NIL"
  | Sexpr(Bool(false)) -> "MAKE_BOOL(0)"
  | Sexpr(Bool(true)) -> "MAKE_BOOL(1)" 
  | Sexpr(Char(x)) -> Printf.sprintf "MAKE_LITERAL_CHAR(%d)" (int_of_char x)
  | Sexpr(String(x)) -> Printf.sprintf "MAKE_LITERAL_STRING \"%s\" " x
  | Sexpr(Number(Int(x))) -> Printf.sprintf "MAKE_LITERAL_INT(%d)" x
  | Sexpr(Number(Float(x))) -> Printf.sprintf "MAKE_LITERAL_FLOAT(%f)" x
  | Sexpr(Pair(x, y)) -> Printf.sprintf "MAKE_LITERAL_PAIR(const_tbl +%d, const_tbl +%d)" (findOffset (Sexpr x) prev_consts_list) (findOffset (Sexpr y) prev_consts_list)
  | Sexpr(Symbol(x)) -> Printf.sprintf "MAKE_LITERAL_SYMBOL(const_tbl +%d)" (findOffset (Sexpr (String x)) prev_consts_list)
  | Sexpr(TagRef(x)) -> "" 
  | _ -> "";;
  

let rec getOffsetSize const = 
  match const with
  | Void -> 1
  | Sexpr(Nil) -> 1
  | Sexpr(Bool(false)) -> 2
  | Sexpr(Bool(true)) -> 2
  | Sexpr(Char(x)) -> 2
  | Sexpr(String(x)) -> (9 + (String.length x)) 
  | Sexpr(Number(Int(x))) -> 9
  | Sexpr(Number(Float(x))) -> 9
  | Sexpr(Pair(x, y)) -> 17
  | Sexpr(Symbol(x)) -> 9
  | Sexpr(TagRef(x)) -> 9
  | _ -> 0;;

let create_final_const curr acc = 
  let first_const_list = get_consts_names curr [] in
  (List.append acc first_const_list);;

let make_pair_consts acc curr = 
  let curr_offset = (match acc with
                     | [] -> 0
                     | (sexp, (offset, assemb))::rest -> (offset + (getOffsetSize sexp))) in
  (curr,(curr_offset, (getAssembly curr acc)))::acc;;

let make_collections acc curr = 
  let curr_collection = get_tagged_collection curr [] in
  List.append acc curr_collection;;

let rec find_in_collection ref collection =
  match collection with
  | [] -> raise X_this_should_not_happen
  | r::rest -> (match r with
                | TaggedSexpr(name, sexp) -> if (name = ref)
                                             then (Sexpr sexp)
                                             else find_in_collection ref rest
                | _ -> raise X_this_should_not_happen)

let rec make_final_table primary_table collection = 
  match primary_table with
  | [] -> primary_table
  | c::rest -> (match c with
                | (Sexpr(TagRef(x)), (offset, _)) -> (Sexpr(TagRef(x)), (offset , (Printf.sprintf "const + %d" (findOffset (find_in_collection x collection) primary_table))))::(make_final_table rest collection)
                | _ -> c::make_final_table rest collection);;


let make_consts_tbl asts = 
  let first_constants = [Void; Sexpr(Nil); Sexpr(Bool(true)) ; Sexpr(Bool(false))] in
  let renamed_asts = rename_tagged_sexp asts in
  let tagged_list = (List.fold_left make_collections [] renamed_asts) in
  let all_consts = List.append first_constants (List.fold_right create_final_const renamed_asts []) in
  let all_const_without_dups = List.rev (remove_dup all_consts []) in
  let second_const_list = expand_const_list all_const_without_dups [] in
  let second_const_without_dups = List.rev (remove_dup second_const_list []) in 
  let primary_table = (List.fold_left make_pair_consts [] second_const_without_dups ) in 
  List.rev (make_final_table primary_table tagged_list);; 
  


(*-------------------------------Free Var Table----------------------------*)
  let rec get_fvar_names expr name_list = 
    match expr with
    | Var'(VarFree(x)) -> x::name_list
    | Box'(var) -> (match var with
                    | VarFree(x) -> x::name_list
                    | _ -> name_list)
    | BoxGet'(var) -> (match var with
                       | VarFree(x) -> x::name_list
                       | _ -> name_list)
    | BoxSet'(var, exp) -> (match var with
                            | VarFree(x) -> List.append (x::name_list) (get_fvar_names exp [])
                            | _ -> get_fvar_names exp name_list) 
    | If'(test, dit, dif) -> (let a = List.append (get_fvar_names test []) (get_fvar_names dit []) in
                              List.append a (get_fvar_names dif name_list))
    | Seq'(exprs) -> (let fvar_per_seq acc curr = List.append acc (get_fvar_names curr []) in
                      List.fold_left fvar_per_seq name_list exprs)
    | Set'(var, value) -> (List.append (get_fvar_names var []) (get_fvar_names value name_list))
    | Def'(var, value) -> (List.append (get_fvar_names var []) (get_fvar_names value name_list))
    | Or'(exprs) -> (let fvar_per_or acc curr = List.append acc (get_fvar_names curr []) in
                      List.fold_left fvar_per_or name_list exprs)
    | LambdaSimple'(args, body) -> get_fvar_names body name_list
    | LambdaOpt'(args, optArg, body) -> get_fvar_names body name_list
    | Applic'(rator, rands) -> (let fvar_per_rand acc curr = List.append acc (get_fvar_names curr []) in
                                let rands_fvar_names = List.fold_left fvar_per_rand [] rands in
                                List.append (get_fvar_names rator name_list) rands_fvar_names)               
    | ApplicTP'(rator, rands) -> (let fvar_per_rand acc curr = List.append acc (get_fvar_names curr []) in
                            let rands_fvar_names = List.fold_left fvar_per_rand [] rands in
                            List.append (get_fvar_names rator name_list) rands_fvar_names) 
    | _ -> name_list;;




 let create_final_fvar name_list counter = 
    let make_fvar_pair curr acc = (let curr_ans = (curr, 8*(fst counter)())::acc in
                                   let _ = (snd counter)() in
                                   curr_ans) in
    List.fold_right make_fvar_pair name_list [];; 



  let make_fvars_tbl asts =  
    let counter = make_counter() in
    let fvar_name_list_func acc curr = (List.append acc (get_fvar_names curr [])) in
    let fvar_name_list = List.fold_left fvar_name_list_func [] asts in
    let prim_list =  ["boolean?"; "float?"; "integer?"; "pair?";"null?"; "char?"; "string?";
   "procedure?"; "symbol?"; "string-length"; "string-ref"; "string-set!"; "make-string"; "symbol->string"; 
   "char->integer"; "integer->char"; "eq?"; "+"; "*"; "-"; "/"; "<"; "="; "car"; "cdr"; "cons"; "set-car!"; "set-cdr!"; "apply"] in
   let final_fvar_names = List.append prim_list fvar_name_list in
   let fvar_without_dup = remove_dup final_fvar_names [] in
   create_final_fvar fvar_without_dup counter;;
 


(*-------------------------generate------------------------ *)
let rec get_fvar_address name f_var_table = 
  match f_var_table with
  | [] -> -1
  | (fvar, offset)::rest -> if (fvar = name)
                            then offset
                            else get_fvar_address name rest;;

let rec get_const_address name const_table = 
  match const_table with
  | [] -> -1
  | (const, (offset, ass))::rest -> if (const = name)
                                    then offset
                                    else get_const_address name rest;;

let generate_extended_env depth c =
    Printf.sprintf "mov	rcx, qword [rbp + 24]		;;;rcx = n
                    cmp	rcx, 0
                    je  emptyA%d				        ;;;n==0? yes- no malloc to A[] needed		        
                    mov rdx, rcx
                    shl rdx, 3				            ;;;rdx = 8*n
                    MALLOC rbx, rdx           ;;;rbx -> a new memory [8*n]  
                    mov rax, rbp
                    add rax, 32     				  ;;;rax -> A[0]
                    mov rdx, 0			        	;;;rdx = 0 (counter)
                  Loop_2%d:                   ;;; rax = pointer to A[i], rbx = pointer to new memory, rcx = n, rdx = i
                    cmp	rdx, rcx				      ;;;i==n? yes - finished
                    je	endLoop_2%d			
                    push rax
                    mov	rax, [rax]	      		;;;rax = A[i]
                    mov [rbx], rax	      		;;;Mem[i] = A[i]
                    add	rbx, 8				        ;;;rbx -> Mem[i+1]
                    pop	rax				
                    add	rax,8		          		;;;rax -> A[i+1]
                    inc rdx					          ;;;i++
                    jmp Loop_2%d
                  endLoop_2%d:
                    shl	rcx, 3
                    sub	rbx, rcx				      ;;; rbx->Mem[0]
                    mov	rcx, %d				        ;;; env_size- d
                    shl rcx, 3  	          	;;; rcx = 8*env_size
                    MALLOC rdx, rcx			      ;;; rdx -> new_env[0]	
                    mov [rdx], rbx			      ;;; new_env[0] = pointer to A[]
                    mov rbx, qword [rbp+16]	  ;;; rbx -> env[0]
                    mov rcx,0				          ;;; i=0 , rcx is counter
                  LoopArgs_2%d:
                    cmp	rcx, %d				        ;;; envSize-1 parameter 
                    je endLoopArgs_2%d
                    add rdx, 8				        ;;; rdx -> new_env[i+1]
                    push rbx
                    mov rbx, [rbx]
                    mov [rdx], rbx
                    pop rbx
                    add rbx, 8				        ;;; rbx -> env[i]
                    inc rcx
                    jmp LoopArgs_2%d
                  endLoopArgs_2%d:
                    shl rcx, 3
                    sub rdx, rcx				      ;;; rdx -> new_env[0]
                    MAKE_CLOSURE (rax, rdx, Lcode%d)
                    jmp Lcont%d
                  emptyA%d:
                    mov	rcx, %d				        ;;; envSize-1
                    cmp rcx, 0                ;;; both sizes 0
                    je bothEmpty%d
                    push rcx
                    shl rcx, 3			          ;;; rcx = 8*env_size
                    MALLOC rbx, rcx			      ;;; rbx -> new_env[0]
                    mov rdx, qword[rbp+16]	  ;;; rdx -> env[0]
                    pop rcx					          ;;; rcx = env_size
                    mov rax,0				          ;;; rax = 0 (counter)
                  emptyA_loop%d:
                    cmp rax, rcx
                    je emptyA_end%d
                    push rdx
                    mov rdx, [rdx]
                    mov [rbx],rdx			      ;;; new_env[i] = env[i]
                    pop rdx
                    add	rdx, 8				        ;;; rdx -> new_env[i+1]
                    add rbx, 8				        ;;; rbx -> env[i+1]
                    inc rax					          ;;; i++
                    jmp emptyA_loop%d
                  bothEmpty%d:
                    mov rbx, SOB_NIL_ADDRESS
                    MAKE_CLOSURE (rax, rbx, Lcode%d)
                    jmp Lcont%d
                  emptyA_end%d:
                    shl rcx, 3
                    sub rdx,rcx				        ;;; rdx -> new_env[0]
                    MAKE_CLOSURE (rax, rdx, Lcode%d)
                    jmp Lcont%d" c c c c c depth c (depth - 1) c c c c c c (depth - 1) c c c c c c c c c c;;

let rec generate_exp const_table f_var_table exp depth counter =
  let _ = (snd counter)() in 
  match exp with
  | Const'(x) -> Printf.sprintf "mov rax, const_tbl +%d" (get_const_address x const_table)
  | Var'(VarParam(_, minor)) -> Printf.sprintf "mov rax, qword [rbp + 8*(4 + %d)]" minor
  | Var'(VarBound(_, major, minor)) -> Printf.sprintf "mov rax, qword [rbp + 8*2] 
                                                       mov rax, qword [rax + 8*%d] 
                                                       mov rax, qword [rax + 8*%d]" major minor
  | Var'(VarFree(x)) -> Printf.sprintf "mov rax, [fvar_tbl +%d]" (get_fvar_address x f_var_table)
  | Set'(Var'(VarParam(_, minor)), e) -> Printf.sprintf "%s 
                                                         mov qword [rbp + 8*(4 + %d)], rax 
                                                         mov rax, SOB_VOID_ADDRESS" (generate_exp const_table f_var_table e depth counter) minor
  | Set'(Var'(VarBound(_, major, minor)), e) -> Printf.sprintf "%s 
                                                                mov rbx, qword [rbp + 8*2] 
                                                                mov rbx, qword [rbx + 8*%d] 
                                                                mov qword [rbx + 8*%d], rax 
                                                                mov rax, SOB_VOID_ADDRESS" (generate_exp const_table f_var_table e depth counter) major minor
  | Box'(var) -> (let generate_var = generate_exp const_table f_var_table (Var' var) depth counter in
                  Printf.sprintf "%s
                                 MALLOC rcx, 8
                                 mov [rcx], rax
                                 mov rax, rcx" generate_var)
  | Set'(Var'(VarFree(x)), e) -> Printf.sprintf "%s 
                                                 mov qword [fvar_tbl +%d], rax 
                                                 mov rax, SOB_VOID_ADDRESS" (generate_exp const_table f_var_table e depth counter) (get_fvar_address x f_var_table)
  | Def'(Var'(VarFree(x)), e) -> Printf.sprintf "%s
                                                 define_lable%d: 
                                                 mov qword [fvar_tbl +%d], rax 
                                                 mov rax, SOB_VOID_ADDRESS" (generate_exp const_table f_var_table e depth counter) ((fst counter)())  (get_fvar_address x f_var_table)
  | Seq'(expList) -> generate_seq const_table f_var_table expList depth counter
  | Or'(expList) -> generate_or const_table f_var_table expList depth counter
  | If'(test, dit, dif) -> let c = (fst counter)() in 
                           (Printf.sprintf "%s 
                                            cmp rax, SOB_FALSE_ADDRESS 
                                            je Lelse%d 
                                            %s 
                                            jmp Lexit%d 
                                            Lelse%d: 
                                            %s 
                                            Lexit%d:" (generate_exp const_table f_var_table test depth counter) c (generate_exp const_table f_var_table dit depth counter) c c (generate_exp const_table f_var_table dif depth counter) c)
  | BoxGet'(x) -> Printf.sprintf "%s 
                                  mov rax, qword [rax]" (generate_exp const_table f_var_table (Var' x) depth counter)
  | BoxSet'(x, e) -> (Printf.sprintf "%s 
                                     push rax 
                                     %s 
                                     pop qword [rax] 
                                     mov rax, SOB_VOID_ADDRESS" (generate_exp const_table f_var_table e depth counter) (generate_exp const_table f_var_table (Var' x) depth counter))
  | LambdaSimple'(args, body) -> (generate_lambda const_table f_var_table body (depth + 1) counter)
  | LambdaOpt'(args, optArg, body) -> (generate_lambda_opt const_table f_var_table exp  (depth + 1) counter)
  | Applic'(rator, rands) -> (generate_applic const_table f_var_table (rator::rands) depth counter) 
  | ApplicTP'(rator, rands) -> (generate_applic_TP const_table f_var_table (rator::rands) depth counter) 
  | _-> raise X_this_should_not_happen

and generate_seq consts_table f_var_table expList depth counter = 
  let _ = (snd counter)() in
  let generate_func acc curr = (let curr_E = generate_exp consts_table f_var_table curr depth counter in
                                Printf.sprintf "%s\n%s" acc curr_E) in 
  List.fold_left generate_func "" expList

and generate_or consts_table f_var_table expList depth counter =
  let _ = (snd counter)() in
  let c = (fst counter)() in
  let epsilon_n = List.hd (List.rev expList) in
  let generated_epsilon_n = generate_exp consts_table f_var_table epsilon_n depth counter in 
  let generate_func acc curr = (let curr_E = generate_exp consts_table f_var_table curr depth counter in
                                Printf.sprintf "%s\n%s 
                                                cmp rax, SOB_FALSE_ADDRESS 
                                                jne Lexit%d" acc curr_E c) in
  let a = List.fold_left generate_func "" (List.rev (List.tl (List.rev expList))) in
  Printf.sprintf "%s 
                  %s 
                  Lexit%d:" a generated_epsilon_n c

and generate_lambda consts_table f_var_table body depth counter =
  let _ = (snd counter)() in
  let c = (fst counter)() in
  Printf.sprintf   "%s
                    MAKE_CLOSURE (rbx, rax, Lcode%d)
                    jmp Lcont%d
                  Lcode%d:
                    push rbp
                    mov rbp, rsp
                    %s
                    leave
                    ret
                  Lcont%d:" (generate_extended_env depth c) c c c (generate_exp consts_table f_var_table body depth counter) c 
  

and generate_lambda_opt consts_table f_var_table lambda depth counter =
  let _ = (snd counter)() in
  let c = (fst counter)() in
  let num_args = (match lambda with
                  | LambdaOpt'(args, optArg, body ) -> ((List.length args) + 1)
                  | _ -> raise X_this_should_not_happen) in
  let body = (match lambda with
              | LambdaOpt'(args, optArg, body ) -> body
              | _ -> raise X_this_should_not_happen) in
  Printf.sprintf  " %s
                  Lcode%d:
                    mov rbx, [rsp + 16]                 ;;;rbx = n
                    cmp rbx, %d                         ;;;cmp rbx numOfArgs
                    jge shrink%d                        ;;;n < numOfArgs
                    mov rsi, rsp                        ;;;rdi - destination
                    mov rcx, rsp                        ;;;rsi - source
                    sub rcx, 8
                    mov rdi, rcx
                    mov rdx, %d                         ;;;bytes = 24+(numArgs-1)*8                        
                    push 0
                    call memmove                        ;;;rax - destination address
                    mov rax, [rsp+16]
                    shl rax, 3
                    add rax, 24
                    add rax, rsp
                    mov qword [rax], SOB_NIL_ADDRESS    ;;;optArg = Nill
                    inc rbx
                    mov [rsp + 16], rbx
                    jmp doNothing%d
                  shrink%d:                             ;;;n >= numOfArgs
                    
                    mov rcx, rbx                        ;;;rcx = n
                    sub rcx, %d                         ;;;rcx = n - numOfArgs --> we need to shrink in to a list
                    mov rbx, [rsp + 16]
                    shl rbx, 3
                    add rbx, 16
                    add rbx, rsp                       ;;;rbx = rsp + allframe
                    mov rdi, [rbx]                     ;;;rdi = args[n]		
                    MAKE_PAIR(rax, rdi, SOB_NIL_ADDRESS)                           
                    mov rdx, rcx                          ;;;rdx = counter
                    dec rdx
                  loopShrink%d:  
                    cmp rdx, 0                        ;;; rcx = opt_args.size
                    je endLoopShrink%d
                    sub rbx, 8
                    mov rdi, [rbx]
                    mov rsi, rax
                    MAKE_PAIR(rax, rdi, rsi)            ;;;Pair(arg[n+i], PrevPair)
                    dec rdx                             ;;;counter--
                    jmp loopShrink%d
                  endLoopShrink%d:                           
                    mov rbx, rax                        ;;;rbx -> array[0]
                    mov rsi, rsp
                    dec rcx
                    shl rcx, 3
                    mov rdx, rcx
                    add rdx, rsp
                    mov rdi, rdx
                    mov rdx, %d                         ;;; rdx = 24 + num_args*8
                    push rbx
                    call memmove
                    pop rbx
                    mov rax, rbp
                    sub rax, 8
                    add rsp, rcx
                    add rdx, rsp
                    mov [rdx], rbx                      ;;;frame[0] = malloc
                    mov qword [rsp + 16], %d            ;;;newN= numArgs
                  doNothing%d:
                    push rbp
                    mov rbp, rsp
                    %s
                    leave
                    ret
                  Lcont%d:" (generate_extended_env depth c) c num_args c (16 + num_args*8) c c (num_args - 1) c c c c (16 + (num_args)*8) num_args c (generate_exp consts_table f_var_table body depth counter) c 
  

and generate_applic consts_table f_var_table rator_rands_list depth counter =
  let _ = (snd counter)() in
  let c = (fst counter)() in
  let rator = (match rator_rands_list with
               | [] -> raise X_this_should_not_happen
               | rator::rands -> rator) in
  let rands = (match rator_rands_list with
               | [] -> raise X_this_should_not_happen
               | rator::rands -> rands) in
  let rands_size = List.length rands in
  let generate_func curr acc = (let generated_curr = (generate_exp consts_table f_var_table curr depth counter) in
                       Printf.sprintf "%s 
                                       %s
                                       push rax" acc generated_curr) in
  let a = List.fold_right generate_func rands "" in
  let generated_rator = (generate_exp consts_table f_var_table rator depth counter) in
  Printf.sprintf   "%s 
                    push %d
                    %s
                    mov sil, byte [rax]
                    cmp sil, T_CLOSURE
                    jne notClosure%d
                    mov rbx, qword [rax + 1]                ;;;rbx = ext_env
                    push rbx
                    mov rbx, qword [rax + 9]                ;;;rbx = Lcode
                    call rbx
                    mov rbx, [rsp + 8]                      ;;; n 
                    add rbx, 2
                    shl rbx, 3
                    add rsp, rbx
                    jmp endApplic%d
                  notClosure%d:
                    ;;;complete with segmentation fault
                  endApplic%d:" a rands_size generated_rator c c c c 

and generate_applic_TP consts_table f_var_table rator_rands_list depth counter =
  let _ = (snd counter)() in
  let c = (fst counter)() in
  let rator = (match rator_rands_list with
               | [] -> raise X_this_should_not_happen
               | rator::rands -> rator) in
  let rands = (match rator_rands_list with
               | [] -> raise X_this_should_not_happen
               | rator::rands -> rands) in
  let rands_size = List.length rands in
  let generate_func curr acc = (let generated_curr = (generate_exp consts_table f_var_table curr depth counter) in
                       Printf.sprintf "%s 
                                       %s
                                       push rax" acc generated_curr) in
  let a = List.fold_right generate_func rands "" in
  let generated_rator = (generate_exp consts_table f_var_table rator depth counter) in                    
    Printf.sprintf "%s 
                    push %d
                    %s
                    mov rdi, rax
                    mov sil, byte [rdi]
                    cmp sil, T_CLOSURE
                    jne notClosure%d
                    mov rbx, qword [rdi + 1]                ;;;rbx = ext_env
                    push rbx
                    push qword [rbp + 8]                ;;; old ret addr
                    push qword [rbp]
                    SHIFT_FRAME %d
                    mov rbx, qword [rdi + 9]                ;;;rbx = Lcode
                    jmp rbx
                    jmp endApplic%d
                  notClosure%d:
                    ;;;complete with segmentation fault
                  endApplic%d:" a rands_size generated_rator c (4 + rands_size)  c c c ;;


let generate consts fvars e = 
  let counter = global_counter in
  (generate_exp consts fvars e 0 counter);;


end;;

(* let fold_func acc curr = 

  let b = tag_parse_expression curr in
  let c = run_semantics b in
  c::acc;;

let test str = 
  let a = read_sexprs str in
  let b = List.fold_left fold_func [] a in
  (* (make_consts_tbl b);;  *)
  let first_constants = [Void; Sexpr(Nil); Sexpr(Bool(true)) ; Sexpr(Bool(false))] in
  let renamed_asts = rename_tagged_sexp b in
  let tagged_list = (List.fold_left make_collections [] renamed_asts) in
  let all_consts = List.append first_constants (List.fold_right create_final_const renamed_asts []) in
  let all_const_without_dups = List.rev (remove_dup all_consts []) in
  let second_const_list = expand_const_list all_const_without_dups [] in
  let second_const_without_dups = List.rev (remove_dup second_const_list []) in 
  let primary_table = (List.fold_left make_pair_consts [] second_const_without_dups ) in 
  List.rev (make_final_table primary_table tagged_list);;  *)
  
