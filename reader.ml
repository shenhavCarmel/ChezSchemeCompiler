
#use "pc.ml";;
open PC;; 

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
type number =
  | Int of int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | TaggedSexpr of string * sexpr
  | TagRef of string;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | TaggedSexpr(name1, expr1), TaggedSexpr(name2, expr2) -> (name1 = name2) && (sexpr_eq expr1 expr2) 
  | TagRef(name1), TagRef(name2) -> name1 = name2
  | _ -> false;;
  
module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

(*Char Parser*)
let char_prefix_parser  = word "#\\";;

let visible_simple_char_parser  = (pack (caten char_prefix_parser (pack (const (fun ch -> ch > ' ')) (fun x -> [x])))
 (fun (x,y) -> Char(List.hd y)));;

let name_char_parser = (caten char_prefix_parser (disj_list [(word_ci "newline"); (word_ci "nul"); (word_ci "page"); (word_ci "return"); (word_ci "space"); (word_ci "tab")]));;

let char_meta_parser  = 
  pack name_char_parser (fun (a,b) -> 
  let b = list_to_string (List.map lowercase_ascii b) in
  match b with
  "newline" -> Char(char_of_int 10) 
  |"nul" -> Char(char_of_int 0)
  |"page" -> Char(char_of_int 12) 
  |"return" -> Char(char_of_int 13)
  |"space" -> Char(char_of_int 32)
  |"tab" -> Char(char_of_int 9 )
  |_ -> raise X_this_should_not_happen);; 

let char_parser = disj char_meta_parser visible_simple_char_parser;;

(*Boolean Parser*)
let boolean_parser_t = word_ci "#t";;
let boolean_parser_f = word_ci "#f";;
let boolPars = disj boolean_parser_t boolean_parser_f;;
let boolean_parser = pack boolPars (fun a -> (if ((list_to_string a) = "#t" || (list_to_string a) = "#T") then (Bool true) else (Bool false)));;

(*Number Parser*)
let digit_parser = range '0' '9';;

let natural_parser = plus digit_parser;;

let plus_parser = char '+';;

let minus_parser = char '-';;

let plus_minus_parser = disj plus_parser minus_parser;; 

let maybe_plus_minus_parser = maybe plus_minus_parser;;

let integerHelp_parser = caten maybe_plus_minus_parser natural_parser;;

let integer_no_none (head,tail) = match head with 
  Some(s) -> s::tail
   |_ -> tail;;

let integer_parser = pack integerHelp_parser integer_no_none;;

let integer_parser_final = pack integer_parser (fun (numStrList) -> Int (int_of_string (list_to_string numStrList)));;

let dot_parser = (word ".");; 

let float_head_parser = caten_list [integer_parser; dot_parser; natural_parser] ;;

let float_parser = pack float_head_parser (fun list -> List.flatten list);;

let float_parser_final = pack float_parser (fun (numStrList) -> Float (float_of_string (list_to_string numStrList)));;

(*String Parser*)
let string_literal_char_parser  = pack (const (fun ch -> ch != '\"' && ch != '\\')) (fun a -> [a]);;

let string_meta_char_parser  = pack (disj_list [(word_ci "\\\\"); (word_ci "\\\""); (word_ci "\\t"); (word_ci "\\f") ; (word_ci "\\n"); (word_ci "\\r")]) 
(fun str -> let b = list_to_string str in
  match b with
  |"\\\\" -> [char_of_int 92] 
  |"\\\"" -> [char_of_int 34]
  |"\\t" -> [char_of_int 9] 
  |"\\f" -> [char_of_int 12]
  |"\\n" -> [char_of_int 10]
  |"\\r" -> [char_of_int 13]
  |_ -> raise X_this_should_not_happen);; 

let string_char_parser  = disj string_meta_char_parser string_literal_char_parser;;

let quotes_parser = pack (char '\"') (fun a -> [a]);;

let string_help_parser  = caten_list [quotes_parser; (pack (star string_char_parser) (fun a -> (List.flatten a))) ; quotes_parser];;

let string_parser  = pack string_help_parser  (fun str -> (String(list_to_string (List.nth str 1))));;  

(*Symbol Parser*)
let symbol_head_parser = disj digit_parser  (pack (range_ci 'a' 'z') (fun ch -> lowercase_ascii ch));;

let symbol_tail_parser = disj_list [(char '!'); (char '$'); (char '^'); (char '*'); (char '-'); (char '_'); (char '='); (char '+'); (char '<'); (char '>'); (char '?'); (char '/'); (char ':')];;

let symbol_parser =
  let symPars = disj symbol_head_parser symbol_tail_parser in
  pack (plus symPars) (fun s -> Symbol(list_to_string s));;

(*the fuctions we got from Meir*)
let make_paired nt_left nt_right nt =
      (let nt = caten nt_left nt in
      let nt = pack nt (function (_, e) -> e) in
      let nt = caten nt nt_right in
      let nt = pack nt (function (e, _) -> e) in
      nt) ;;

 let make_spaced nt =
  make_paired (star nt_whitespace) (star nt_whitespace) nt;;  

(*final number Parser*)
let number_parser_for_scientific = pack (disj_list [float_parser_final; integer_parser_final]) (fun a-> Number(a));; 

let number_parser = not_followed_by number_parser_for_scientific symbol_parser ;;


(*scientific Notation Parser*)
let scientific_notation_parser = 
  let right_side = pack (caten (char_ci('e')) number_parser) (fun (e,num) -> num) in
  let notation_num_parser = caten number_parser_for_scientific  right_side in
  pack notation_num_parser (function (num,power) -> match num,power with
                                                  | Number(Float(x)),Number(Int(y)) -> Number(Float(x *. (10.0 ** float(y))))                                          
                                                  | Number(Int(x)),Number(Int(y)) -> Number(Float(float(x) *. (10.0 ** float(y))))   
                                                  | _,Number(Float(x)) -> raise X_this_should_not_happen   
                                                  | _ -> raise X_this_should_not_happen);;  

(*Radix Parser*)
let convert_char base char = 
    (let a = (int_of_char char) in
    let converted_a = (if(a >= (int_of_char '0') && a <= (int_of_char '9'))
                       then (a - (int_of_char '0'))
                       else if (a >= (int_of_char 'a') && a <= (int_of_char 'z'))
                            then (a - (int_of_char 'a') + 10)
                            else if (a >= (int_of_char 'A') && a <= (int_of_char 'Z'))
                                 then (a - (int_of_char 'A') + 10)
                                 else raise X_this_should_not_happen) in
    if(converted_a <= base)
    then converted_a
    else raise X_this_should_not_happen) ;;

let calculate_int_radix sign base leftNum = 
  let fold_func a b = ((a + b) * base) in
  (sign * ((List.fold_left fold_func 0 (List.map (convert_char base) leftNum)) / base));;

let calculate_float_radix sign base leftNum rightNum = 
  let fold_func a b = ((a +. b) /. float(base)) in
  let right_hand_side = (List.fold_right fold_func (List.map (fun element -> float(convert_char base element)) rightNum) 0.0) in
  (* (float(sign) *. ((float(calculate_int_radix 1 base leftNum) +. (float(base) *. right_hand_side))));;  *)
  (float(sign) *. ((float(calculate_int_radix 1 base leftNum) +. right_hand_side)));; 

 let radix_parser = 
      let radix_header_parser = pack (caten (char '#') natural_parser) (fun (hashtag,num)-> num) in
      let base_parser = pack (caten radix_header_parser (char_ci 'r')) (fun (num,r) -> num) in
      let n_parser = (plus (disj_list [digit_parser; (range 'a' 'z'); (range 'A' 'Z')])) in
      let full_n_parser = caten (maybe (disj (char '+') (char '-'))) (caten n_parser (maybe (caten (char '.') n_parser))) in
      let radix_num_helper_parser = caten base_parser full_n_parser  in
      pack radix_num_helper_parser (fun (base,number) -> (if ((int_of_string (list_to_string base)) > 36 || (int_of_string (list_to_string base)) < 2)
                                                                                then raise X_this_should_not_happen
                                                                                else let numSign = match number with
                                                                                                |(Some('-'),rest) -> -1
                                                                                                |(Some('+'),rest) -> 1
                                                                                                |(None,rest) -> 1 
                                                                                                |_ -> raise X_this_should_not_happen in
                                                                                  match number with 
                                                                                  | (sign,(leftNum,None)) -> Number(Int(calculate_int_radix numSign (int_of_string (list_to_string base)) leftNum))
                                                                                  | (sign,(leftNum,(Some('.', rightNum)))) -> Number(Float(calculate_float_radix numSign (int_of_string (list_to_string base)) leftNum rightNum))
                                                                                  | _ -> raise X_this_should_not_happen));;
 
(* Sexp Parse *)
let rec sexp_parser s =
  let ignore_comments_parsers = star (disj_list [pack nt_whitespace (fun a -> []); sexp_comment_parser; line_comment_parser]) in
  let parser = (disj_list [char_parser; boolean_parser; scientific_notation_parser; radix_parser; number_parser; string_parser; symbol_parser; list_parser; dotted_list_parser; quote_parser; quasi_quote_parser; unquoted_parser; unquote_and_spliced_parser; tagged_exp_parser; tag_parser]) in
  ((make_paired ignore_comments_parsers ignore_comments_parsers parser) s) 

(*Lists Parser*)
and list_parser s = 
    let ignore_comments_parsers = star (disj_list [(pack nt_whitespace (fun a -> [] ));sexp_comment_parser; line_comment_parser]) in
    let left_side = make_paired ignore_comments_parsers ignore_comments_parsers (word "(") in
    let right_side = make_paired ignore_comments_parsers ignore_comments_parsers (word ")") in
    let listPars = make_paired left_side right_side (star (make_spaced sexp_parser)) in
    let listPred lst = (List.fold_right (fun curr acc ->  Pair(curr, acc)) lst Nil) in
    pack listPars listPred s

and dotted_list_parser s =
  let dotted_list_head_parser = plus (make_spaced sexp_parser) in
  let dotted_list_tail_parser = pack (caten (make_spaced (char '.')) (make_spaced sexp_parser)) (fun (dot,sexp) -> sexp) in
  let both_parsers = caten dotted_list_head_parser dotted_list_tail_parser in
  let dlist_parser = make_paired (make_spaced (word "(")) (make_spaced (word ")")) (make_spaced both_parsers) in 
  pack dlist_parser (fun (sexps , last_sexp) -> (List.fold_right (fun acc curr ->  Pair(acc,curr)) sexps last_sexp)) s

(*Quote and friends Parser*)
and quote_parser s = 
  let quotePars =  make_paired (make_spaced (char '\'')) (make_spaced nt_epsilon) sexp_parser in
  let quotePred sexp = Pair(Symbol("quote") , Pair(sexp , Nil)) in
  pack quotePars quotePred s

and quasi_quote_parser s = 
  let quasiQuotePars =  make_paired (make_spaced(char '`')) (make_spaced nt_epsilon) sexp_parser in
  let quasiQuotePred sexp = Pair(Symbol("quasiquote") , Pair(sexp , Nil)) in
  pack quasiQuotePars quasiQuotePred s

and unquoted_parser s = 
  let unquotedPars =  make_paired (make_spaced(char ',')) (make_spaced nt_epsilon) sexp_parser in
  let unquotedPred sexp = Pair(Symbol("unquote") , Pair(sexp , Nil)) in
  pack unquotedPars unquotedPred s

and unquote_and_spliced_parser s = 
  let unquoteAndSplicedPars =  make_paired (make_spaced(word ",@")) (make_spaced nt_epsilon) sexp_parser in
  let unquoteAndSplicedPred sexp = Pair(Symbol("unquote-splicing") , Pair(sexp , Nil)) in
  pack unquoteAndSplicedPars unquoteAndSplicedPred s

(*Tag Parser*)
and tag_parser s =
  let tagPars = make_paired (make_spaced (word "#{")) (make_spaced (word "}"))  symbol_parser in
  pack tagPars (fun tag -> match tag with 
                          | Symbol(x)-> TagRef(x)
                          |_->raise X_this_should_not_happen) s

and tagged_exp_parser s =
  let tagged_exp_tail_parser = caten (char '=') sexp_parser in
  let tagged_helper =  caten tag_parser (maybe tagged_exp_tail_parser) in
  pack tagged_helper (fun x -> match x with
                              |(tag, None) -> tag
                              |(TagRef(x),Some(equal,sexp)) -> TaggedSexpr(x,sexp)
                              |_ -> raise X_this_should_not_happen) s 

(*Comments Parser*)
and line_comment_parser s = 
  let comment_body_parser = (star (diff nt_any (char '\n'))) in
  let end_comment_parser = disj (word "\n") nt_end_of_input in
  let all_comment_parser = caten_list [(word ";"); comment_body_parser; end_comment_parser] in
  pack all_comment_parser (fun comment -> []) s 

and sexp_comment_parser s = 
  let comment_header = (word "#;") in
  let comment_parser = caten comment_header (make_spaced sexp_parser) in
  pack comment_parser (fun comment -> []) s

and check_if_name_exist taggedList name = 
  let curr_fun = (fun newTag -> newTag = name) in
  (List.exists curr_fun taggedList)
  
and tagged_checker parsed taggedList =  
  match parsed with 
  | TaggedSexpr(name,sexp) -> (if(check_if_name_exist taggedList name) 
                               then raise X_this_should_not_happen
                               else tagged_checker sexp (name::taggedList))
  | Pair(left,right) -> (let _ = (tagged_checker right taggedList) in
                                     (tagged_checker left taggedList))
  | _ -> parsed;;


let read_sexpr string = 
  let string_list = (string_to_list string) in
  let result = sexp_parser string_list in
  match result with
  |(parsed,[]) -> (let _ = (tagged_checker parsed []) in
                  parsed)
  |_ -> raise X_this_should_not_happen;; 

let read_sexprs string = 
  let string_list = (string_to_list string) in
  let result = (star sexp_parser) string_list in 
  match result with
  |(parsed,[]) -> (let _ = List.map (fun parsedSexp -> (tagged_checker parsedSexp [])) parsed in
                   parsed)
  |_ -> raise X_not_yet_implemented;;

end;; (* struct Reader *)
(* Reader.read_sexpr "#{x}=(#{x}=1 . 1) #t 123";;  *)

