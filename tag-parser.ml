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
  (* val symbol_extract_fun : string list -> sexpr -> string list *)
  (* val implicit_seq : expr list -> sexpr -> expr list *)
  val tag_pareser : sexpr -> expr

  val tag_parse_expressions : sexpr list -> expr list
  


end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "pset!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)


(* define is a reserved ward that no var can have = therefore we put it in the hd of the list*)
(* to sign that we have LambdaOpt *)

let rec symbol_extract_fun lst sexpr = match sexpr with
  | Nil -> lst
  | Pair(Symbol(s),Symbol(end_of_list)) -> if(not ((List.mem s lst) || (List.mem s reserved_word_list))) 
                                            then (symbol_extract_fun (lst@[s]) (Symbol(end_of_list)))
                                            else raise X_syntax_error
  | Pair(Symbol(s),rest) -> if(not ((List.mem s lst) || (List.mem s reserved_word_list))) then (symbol_extract_fun (lst@[s]) rest) else raise X_syntax_error
  | Symbol(end_of_list) -> if(not ((List.mem end_of_list lst) || (List.mem end_of_list reserved_word_list))) then  (["define"; end_of_list]@lst) else raise X_syntax_error
  | _ -> raise X_syntax_error;;




  
let rec tag_pareser sexpr = match sexpr with
  | Bool(s) -> Const(Sexpr(sexpr))
  | Number(s) -> Const(Sexpr(sexpr))
  | Char(s) -> Const(Sexpr(sexpr))
  | String(s) -> Const(Sexpr(sexpr))
  | Pair(Symbol "quote", Pair(sexpr, Nil)) -> Const(Sexpr(sexpr))
  | Nil -> Const(Void)

  | Symbol(s) -> if (not (List.mem s reserved_word_list)) then Var(s) else  raise X_no_match

  (* ============================= IF ============================================= *)  

  | Pair(Symbol "if", Pair(test_sexp, Pair(then_sexp, Pair(else_sexp, Nil)))) ->
      let test_exp = (tag_pareser test_sexp) in
      let then_exp = (tag_pareser then_sexp) in
      let else_exp = (tag_pareser else_sexp) in
      If(test_exp, then_exp, else_exp)
  
  | Pair(Symbol "if",Pair(test_sexp,Pair(then_sexp ,Nil))) ->
      let test_exp = tag_pareser test_sexp in
      let then_exp = tag_pareser then_sexp in
      If(test_exp, then_exp, Const(Void))


(* ====================== COND ======================================== *)
(* (cond (a => (b 2)) (else 1)) *)

  | Pair(Symbol "cond", cases) -> 
    let rec cond_exp case = match case with
      | Pair(Pair(Symbol "else", else_sexp),_) -> 
                      (Pair(Symbol "begin", else_sexp))



      | Pair(Pair( value, Pair(Symbol "=>", Pair(function_sexp ,Nil) )) , Nil) ->
                                            
                      (Pair(Symbol "let", Pair(
                        Pair(Pair(Symbol "value", Pair(value, Nil)),
                        Pair(Pair(Symbol "f", Pair(Pair(Symbol "lambda", Pair(Nil, Pair(function_sexp, Nil))), Nil)),
                        Nil)),
                        Pair(Pair(Symbol "if", Pair(Symbol "value", Pair(Pair(Pair(Symbol "f", Nil), Pair(Symbol "value", Nil)), Nil))), Nil))))
                          

      | Pair(Pair( value, Pair(Symbol "=>", Pair(function_sexp ,Nil) )) , recursive_more) ->
                                            
                      (Pair(Symbol "let", Pair(
                        Pair(Pair(Symbol "value", Pair(value, Nil)),
                        Pair(Pair(Symbol "f", Pair(Pair(Symbol "lambda", Pair(Nil, Pair(function_sexp, Nil))), Nil)),
                        Pair(Pair(Symbol "rest", Pair(Pair(Symbol "lambda", Pair(Nil, Pair((cond_exp recursive_more), Nil))), Nil)), Nil))),
                        Pair(Pair(Symbol "if", Pair(Symbol "value", Pair(Pair(Pair(Symbol "f", Nil), Pair(Symbol "value", Nil)), Pair(Pair(Symbol "rest", Nil), Nil)))), Nil))))
                             
                       

      | Pair(Pair(test_sexp, then_sexp), Pair(Pair(Symbol "else", else_sexp),Nil)) ->
                       (Pair(Symbol("if"),Pair(test_sexp,Pair(Pair(Symbol "begin", then_sexp),Pair(Pair(Symbol "begin", else_sexp),Nil)  )))) 
      | Pair(Pair(test_sexp, then_sexp), Nil) -> 
                       (Pair(Symbol("if"),Pair(test_sexp,Pair(Pair(Symbol "begin", then_sexp),Nil )))) 


      | Pair(Pair(test_sexp, then_sexp), recursive_more) ->
                       (Pair(Symbol("if"),Pair(test_sexp,Pair(Pair(Symbol "begin", then_sexp),Pair((cond_exp recursive_more)        ,Nil) ))))
                       
                       | _ -> raise X_no_match
      
                       
      in (tag_pareser (cond_exp cases))


  (* ================================= LAMBDA ============================================= *)
   

  | Pair(Symbol "lambda", Pair(params, body)) ->  
        let params_string_list = (symbol_extract_fun [] params) in 
        let bodies = (implicit_seq body) in
        if((List.length params_string_list) == 0) 
                then LambdaSimple(params_string_list, bodies) 

                (* define is a reserved ward that no var can have = therefore we put it in the hd of the list*)
                (* to sign that we have LambdaOpt *)

                else if (String.equal (List.hd params_string_list) "define") 
                  then LambdaOpt((List.tl (List.tl params_string_list)), (List.hd (List.tl params_string_list)), bodies )
                  else LambdaSimple(params_string_list, bodies)

(* =================================== OR =============================================== *)

  | Pair(Symbol "or", s) -> 
      let rec expr_list lst sexpr = match sexpr with
      | Nil -> lst
      | Pair(s ,rest) -> (expr_list (lst@[(tag_pareser s)]) rest)
      | _ -> raise X_no_match
      in
      (* if (s==Nil) then Const(Sexpr(Bool(false))) else Or(expr_list [] s) *)
      let conds = match s with
      | Nil -> Const(Sexpr(Bool(false)))
      | Pair(exp ,Nil) -> (tag_pareser exp)
      | _ -> Or(expr_list [] s)
      in 
      conds

(* ================================== DEFINE =================================================== *)
(* macro *)
  | Pair(Symbol "define", Pair(     Pair(Symbol(var), var_list ),   Pair(sexpr_plus, Nil)  )) -> 
          let name_exp = tag_pareser (Symbol(var)) in
          let def_exp = match name_exp with 
            (* | Var(s),Applic(app, lic) -> Def(var_exp,app)  *)
            | Var(s)-> Def(name_exp,   tag_pareser  (Pair(Symbol "lambda", Pair(var_list, Pair(sexpr_plus, Nil)))))
            | _ -> raise X_no_match in
      def_exp
(* original *)
  | Pair(Symbol "define", Pair(var, sexpr)) -> 
    let var_exp = tag_pareser var in
    let sexpr_exp = tag_pareser sexpr in
    let def_exp = match var_exp, sexpr_exp with 
      | Var(s),Applic(app, []) -> Def(var_exp,app) 
      | Var(s),_-> Def(var_exp,sexpr_exp) 
      | _ -> raise X_no_match in
    def_exp






    (* =========================================== SET! ========================================== *)

  | Pair(Symbol "set!",Pair(var, Pair(tl , Nil))) ->
    let var_exp = tag_pareser var in
    let tl_exp = tag_pareser tl in
    let set_exp = match var_exp with
      | Var(s) -> Set(var_exp,tl_exp)
      | _ -> raise X_no_match in
    set_exp


(* =============================== PSET!====================================================== *)

(* (pset! (x y) (y x)) *)

| Pair(Symbol "pset!", pairs) ->
    
    let gen_var s num = String.concat "" [s; string_of_int num] in

    let rec lambda_vars params num = match params with
    |Pair(Pair(Symbol(s), Pair(val_sexp, Nil)), Nil) -> Pair(Symbol(gen_var s num), Nil)
    |Pair(Pair(Symbol(s), Pair(val_sexp, Nil)), ribs) -> Pair(Symbol(gen_var s num), (lambda_vars ribs (num + 1)))
    | _ -> raise X_no_match in


    let rec body_sets pairs num = match pairs with
    |Pair(Pair(Symbol(s), Pair(val_sexp, Nil)), Nil) ->   Pair(Pair(Symbol "set!", Pair(Symbol(s) , Pair(Symbol(gen_var s num) , Nil))), Nil)
    |Pair(Pair(Symbol(s), Pair(val_sexp, Nil)), ribs) ->  Pair(Pair(Symbol "set!", Pair(Symbol(s) , Pair(Symbol(gen_var s num) , Nil))), (body_sets ribs (num + 1)))                                                          
    | _ -> raise X_no_match in

  

    let rec applic_vars lst pairs = match pairs with
    |Pair(Pair(Symbol(s), Pair(val_sexp, Nil)), Nil) -> lst@[(tag_pareser val_sexp)]
    |Pair(Pair(Symbol(s), Pair(val_sexp, Nil)), ribs) -> (applic_vars (lst@[(tag_pareser val_sexp)]) ribs)
    | _ -> raise X_no_match in


    let gen_vars = lambda_vars pairs 0 in 
    let gen_body = body_sets pairs 0 in 
    let gen_applic_vals = applic_vars [] pairs in
    
    Applic(tag_pareser (Pair(Symbol "lambda",Pair(gen_vars ,gen_body))) , gen_applic_vals)  
    
    
    
(* ====================================== BEGIN =============================================== *)



    | Pair(Symbol "begin", s) -> 
    let rec expr_list lst sexpr = match sexpr with
    | Nil -> lst
    | Pair( Pair(Symbol "begin", Pair(s, rest1)), rest2) -> (expr_list (expr_list (lst@[(tag_pareser s)]) rest1) rest2)
    | Pair(s ,rest) -> (expr_list (lst@[(tag_pareser s)]) rest)
    | _ -> raise X_no_match
    in
    let conds = match s with
    | Nil -> Const(Void)
    | Pair(exp ,Nil) -> tag_pareser exp
    | _ -> Seq(expr_list [] s)
    in 
    conds

(* ==================================== AND ================================================= *)

    | Pair(Symbol "and", s) -> 
      let and_exp = match s with
        | Nil -> Const(Sexpr(Bool(true)))
        | Pair(exp ,Nil) -> (tag_pareser exp)
        | Pair(s , rest) -> 
          let hd = tag_pareser s in
          let and_to_if = tag_pareser (Pair(Symbol "and",rest)) in 
          If(hd, and_to_if, Const(Sexpr(Bool(false))))
        | _ -> raise X_no_match
      in 
      and_exp

(* ===================================== LET ================================================ *)

      
    | Pair(Symbol "let", Pair( params, body)) -> 
        let rec vars_exps params = match params with
          | Nil -> Nil  
          (* | Pair(Nil, Nil) -> Nil *)
          | Pair(Pair(var_sexp, val_sexp), Nil) -> Pair(var_sexp,Nil)
          | Pair(Pair(var_sexp, val_sexp), ribs) -> Pair(var_sexp, (vars_exps ribs))
          
          | _ -> raise X_no_match
        in
        let rec vals_exps params = match params with
          | Nil -> Nil
          (* | Pair(Nil, Nil) -> Nil *)
          | Pair(Pair(var_sexp, Pair(val_sexp,Nil)), Nil) -> Pair(val_sexp,Nil)
          | Pair(Pair(var_sexp, Pair(val_sexp,Nil)), ribs) -> Pair(val_sexp, (vals_exps ribs))
          
          | _ -> raise X_no_match


        in
        let rec app_params lst sexpr = match sexpr with
          | Nil -> lst
          | Pair(s ,rest) -> (app_params (lst@[(tag_pareser s)]) rest)
          
          | _ -> raise X_no_match
        in
        let lambda_vars = vars_exps params in
        let lambda_vals = vals_exps params in
        let lambda_vals_pairs_converted_to_array = (app_params [] lambda_vals) in
        Applic((tag_pareser (Pair(Symbol "lambda",Pair(lambda_vars,body)))) , lambda_vals_pairs_converted_to_array)




 (* ================================== LET* =================================================== *)

      
 | Pair(Symbol "let*", Pair( params, body)) -> 
      let rec let_options params = match params with
          | Nil -> 
                            tag_pareser (Pair(Symbol "let", Pair( params, body)))
          | Pair(Pair(var_sexp, Pair(val_sexp,Nil)), Nil) ->
                            tag_pareser (Pair(Symbol "let", Pair( params, body)))                   
          | Pair(Pair(Symbol(var_string), Pair(val_sexp,Nil)), ribs) -> 

          Applic(  LambdaSimple([var_string] , (tag_pareser (Pair(Symbol "let*", Pair( ribs, body)))))  , [(tag_pareser val_sexp)])

          | _ -> raise X_no_match
          in  (let_options params)


(* ====================================== LETREC =============================================== *)

          
 


| Pair(Symbol "letrec", Pair(params, body)) ->
      let rec f_whatevers params = match params with
        |Pair(Pair(Symbol(s), Pair(val_sexp, Nil)), Nil) -> Pair(Pair(Symbol(s), Pair(Pair(Symbol "quote", Pair(Symbol "whatever", Nil)), Nil)), Nil)
        |Pair(Pair(Symbol(s), Pair(val_sexp, Nil)), ribs) -> Pair(Pair(Symbol(s), Pair(Pair(Symbol "quote", Pair(Symbol "whatever", Nil)), Nil)), f_whatevers ribs )        
        | _ -> raise X_no_match
      in
        let rec set_exps_init params body = match params with
        |Pair(Pair(Symbol(s), Pair(val_sexp, Nil)), Nil) ->   Pair(Pair(Symbol "set!", Pair(Symbol(s) , Pair(val_sexp , Nil))),  Pair(Pair(Symbol "let", Pair(Nil, body )), Nil))                
        |Pair(Pair(Symbol(s), Pair(val_sexp, Nil)), ribs) ->  Pair(Pair(Symbol "set!", Pair(Symbol(s) , Pair(val_sexp , Nil))), set_exps_init ribs body)                                                          
        | _ -> raise X_no_match

        in
        let f_whatever_applied = f_whatevers params in
        let set_exps_init_applied = set_exps_init params body in

  tag_pareser  (Pair(Symbol "let", Pair(  f_whatever_applied, set_exps_init_applied  )))



(* ======================================== QUASI ============================================= *)


  | Pair(Symbol "quasiquote",Pair (quasi_exp, Nil)) -> 
        let rec ans exp = match exp with 
          | Nil -> Pair(Symbol("quote"),Pair(Nil,Nil))
          | Pair(Symbol "unquote",Pair (exp, Nil)) -> exp
          | Pair(Symbol "unquote-splicing",Pair (exp, Nil)) -> raise X_no_match
          | Symbol(s) -> Pair(Symbol ("quote"), Pair(Symbol(s), Nil))
          | Pair(Pair(Symbol "unquote-splicing", Pair (car, Nil)), cdr) ->
              Pair(Symbol("append"),Pair(car ,Pair((ans cdr),Nil)))
          | Pair(car ,Pair(Symbol "unquote-splicing", Pair (cdr, Nil))) -> 
              Pair(Symbol("cons"),Pair(ans car,Pair(cdr,Nil)))

          | Pair(car,cdr) -> 
              Pair(Symbol "cons", Pair(ans car, Pair(ans cdr, Nil)))
          (* | _ -> raise X_no_match *)
          | _ -> exp
        in
        tag_pareser (ans quasi_exp)


(* ================================ APPLIC ===================================================== *)

  
  | Pair(applic, params) -> 
      let proc_exp = tag_pareser applic in
      let rec params_exp lst sexpr = match sexpr with
        | Nil -> lst
        | Pair(s ,rest) -> (params_exp (lst@[(tag_pareser s)]) rest)
        | _ -> raise X_no_match
      in
      Applic(proc_exp, (params_exp [] params))
  

  (* ===================================== IMPLICIT_SEQ ================================================ *)
  
  (* implicit sequences mustcontain at least one element. *)
and implicit_seq sexpr = 
  let rec implicit lst sexpr = match sexpr with
  | Pair(some, Nil) ->  (lst@[(tag_pareser some)])
  | Pair(some, more) -> (implicit (lst@[(tag_pareser some)]) more)
  | _ -> raise X_no_match
  in
  let conds = match sexpr with
  (* maybe this one should not be seq but this way only works *)
    | Pair(some ,Nil) -> tag_pareser some
    (* | Pair(some ,Nil) -> (tag_pareser (Pair(some ,Nil))) *)

    | _ -> Seq(implicit [] sexpr)
    in 
    conds;;

  
(* ===================================================================================== *)
(* ===================================================================================== *)

let tag_parse_expressions sexpr = List.map tag_pareser sexpr;;


  
end;; (* struct Tag_Parser *)
open Tag_Parser;;

  




   
