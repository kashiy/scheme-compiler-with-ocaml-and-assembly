#use "semantic-analyser.ml";;


exception X_procces_const;;
exception X_return_address_in_const_table;;
exception X_return_address_in_fvar_table;;
exception X_define_param_bound_in_fvar_tbl;;
exception X_generate;;



(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig

  

  val map_flatten_func : 'a list list -> 'a list -> 'a list
  val procces_const : expr' -> constant list
  val remove_duplicates_func : 'a list -> 'a list 
  val allocate_mem_func : constant list -> (constant * (int * string)) list 
  
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val return_address_in_const_table_func : ('a * (int * 'b)) list -> 'a -> string

  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  


  val procces_fvar : expr' -> string list
  val allocate_mem_fvar_func : 'a list -> ('a * int) list
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
  val generate_helper : (constant * (int * string)) list -> (string * int) list -> expr' -> string
  val run_gen : expr' list -> string 

  val one_to_three : string -> expr' list
end;;

module Code_Gen : CODE_GEN = struct
  (* let make_consts_tbl asts = raise X_not_yet_implemented;; *)





  (* val return_address_in_const_table_func : ('a * (int * 'b)) list -> 'a -> string *)

  let return_address_in_const_table_func table const_param =
    let rec return_address_in_const_table table const_param = match table with
    | [] -> raise X_return_address_in_const_table
    | _ ->  check_hd_table (List.hd table) (List.tl table) const_param

    and check_hd_table head tail const_param =
      let (a,(b,c)) = head in
      (* match a with *)
      (* | const_param -> (string_of_int b)
      | _ ->return_address_in_const_table tail const_param *)
      if (a = const_param) then (string_of_int b) else return_address_in_const_table tail const_param

    in return_address_in_const_table table const_param;;


    (* return index in fvar_table_func *)
  let return_index_in_fvar_table_func table fvar_param =
    let rec return_address_in_fvar_table table fvar_param = match table with
    | [] -> raise X_return_address_in_fvar_table
    | _ ->  check_hd_table (List.hd table) (List.tl table) fvar_param

    and check_hd_table head tail fvar_param =
      let (a,b) = head in
      if (a = fvar_param) then (string_of_int b) else return_address_in_fvar_table tail fvar_param

    in return_address_in_fvar_table table fvar_param;;





(* val map_flatten_func : 'a list list -> 'a list -> 'a list = <fun> *)

(* get a list and empty arr and return a flutten "map" *)
(* for symbol we insert his string and the relevant symbol that point him*)
(* for pair we insert recursivly car and cdr, and then insert the pair as well *)
let rec map_flatten_func map res = match map with
  | [] -> res
  | _ ->  (map_flatten_func (List.tl map) (res@(List.hd map)) );;
  
let procces_const expr = 
  let rec consts expr arr = match expr with
    | Const'(Sexpr(Symbol(s1)))-> 
                            arr@[(Sexpr(String(s1))); (Sexpr(Symbol(s1)))]
    | Const'(Sexpr(Pair(car, cdr)))->
                            arr@ (consts (Const'(Sexpr(car))) []) @ (consts (Const'(Sexpr(cdr))) []) @ [(Sexpr(Pair(car, cdr)))]
    
    | Const'(s1)->          arr@[s1]
    
    | Var'(v1)->            arr
    | Box'(v1)->            arr
    | BoxGet'(v1)->         arr
    | BoxSet'(v1,e1) ->     (consts e1 arr)
    | If'(t1, th1, el1)->   (consts t1 arr) @ (consts th1 []) @ (consts el1 [])
    | Seq'(l1) ->
                            let apply_consts_with_map single = consts single [] in
                            let map_seq = List.map apply_consts_with_map l1 in
                            let flattened = (map_flatten_func map_seq []) in
                            arr@flattened
    | Or'(l1) ->
                            let apply_consts_with_map single = consts single [] in
                            let map_or = List.map apply_consts_with_map l1 in
                            let flattened = (map_flatten_func map_or []) in
                            arr@flattened
    | Set'(var, val1) ->     (consts val1 arr)
    | Def'(var, val1)->      (consts val1 arr)
    | LambdaSimple'(vars, body)->
                            (consts body arr)
    | LambdaOpt'(vars, var, body) ->
                            (consts body arr)
    | Applic'(proc, args) ->
                            let apply_consts_with_map single = consts single [] in
                            let map_args = List.map apply_consts_with_map args in
                            let flattened = (map_flatten_func map_args []) in
                            (consts proc arr) @ flattened
    | ApplicTP'(proc, args) ->
                            let apply_consts_with_map single = consts single [] in
                            let map_args = List.map apply_consts_with_map args in
                            let flattened = (map_flatten_func map_args []) in
                            (consts proc arr) @ flattened
    (* | _ -> raise X_procces_const *)
    in 
    consts expr [];;



    
    

let remove_duplicates_func arr_with_dups = 
  let rec remove_duplicates arr res = match arr with
  | [] -> res
  | _ ->  
          let head = (List.hd arr) in
          let tail = (List.tl arr) in
          let does_hd_exist_in_res = List.mem head res in
          if (does_hd_exist_in_res) then (remove_duplicates tail res) else (remove_duplicates tail (res@[head]))
  in 
  remove_duplicates arr_with_dups [];;


  

let allocate_mem_func arr_without_dups = 
  let rec allocate_mem arr res index = match arr with
  | [] -> res
  | _ ->  
          let head = (List.hd arr) in
          let tail = (List.tl arr) in 
          caten_head head tail res index

  and caten_head hd arr res index = match hd with
  | Void ->               (allocate_mem arr (res@[(Void, (index, "MAKE_CONST_VOID\n"))]) (index + 1))
  | Sexpr(Nil) ->         (allocate_mem arr (res@[(Sexpr(Nil), (index, "MAKE_CONST_NIL\n"))]) (index + 1))
  | Sexpr(Bool false) ->  (allocate_mem arr (res@[(Sexpr(Bool false), (index, "MAKE_LITERAL_BOOL(0)\n"))]) (index + 2))
  | Sexpr(Bool true) ->   (allocate_mem arr (res@[(Sexpr(Bool true), (index, "MAKE_LITERAL_BOOL(1)\n"))]) (index + 2))
  | Sexpr(Char(c1))->     (allocate_mem arr (res@[(hd, (index,( String.concat "" ["MAKE_LITERAL_CHAR(";string_of_int ((int_of_char c1));")\n"])))]) (index + 2))
  | Sexpr(Number(Float f1)) ->
                          (allocate_mem arr (res@[(hd, (index,( String.concat "" ["MAKE_LITERAL_FLOAT(";(string_of_float f1);")\n"])))]) (index + 9))
  | Sexpr(Number(Fraction (n1, d1))) ->
                          (allocate_mem arr (res@[(hd, (index,( String.concat "" ["MAKE_LITERAL_RATIONAL("; string_of_int n1; ", "; string_of_int d1; ")\n"])))]) (index + 17))
  | Sexpr(String(s1)) ->  (allocate_mem arr (res@[(hd, (index,( String.concat "" ["MAKE_LITERAL_STRING \"";s1; "\"\n"])))]) (index + 9 + (String.length s1)))
  (* | Sexpr(String(s1)) ->  (allocate_mem arr (res@[(hd, (index,( String.concat "" ["MAKE_LITERAL_STRING(";s1;")"])))]) (index + 9 + (String.length s1))) *)
  | Sexpr(Symbol(s1)) ->  
                          let address_of_the_string = return_address_in_const_table_func res (Sexpr(String(s1))) in
                          (allocate_mem arr (res@[(hd, (index,( String.concat "" ["MAKE_LITERAL_SYMBOL(const_tbl+";address_of_the_string;")\n"])))]) (index + 9))
  
  | Sexpr(Pair(car, cdr)) ->
                          let address_of_the_car = (return_address_in_const_table_func res (Sexpr(car))) in   
                          let address_of_the_cdr = (return_address_in_const_table_func res (Sexpr(cdr))) in
                          (allocate_mem arr (res@[(hd, (index,( String.concat "" ["MAKE_LITERAL_PAIR(const_tbl+"; address_of_the_car; ",const_tbl+"; address_of_the_cdr; ")\n"])))]) (index + 17))
  in
  allocate_mem arr_without_dups [] 0 ;;
  

      
  (* let make_consts_tbl asts = (allocate_mem_func (remove_duplicates_func (procces_const asts) ));; *)
  let make_consts_tbl asts = 
    let add_void_nil_boolTF = [Void;Sexpr(Nil);Sexpr(Bool false);Sexpr(Bool true)] 
    in
    (allocate_mem_func (remove_duplicates_func  (add_void_nil_boolTF @ ( map_flatten_func (List.map procces_const asts) []) )));;
  
  (* let make_consts_tbl asts = raise X_not_yet_implemented;; *)

  (*let make_consts_tbl asts = raise X_not_yet_implemented;; *)




  let procces_fvar expr = 
    let rec fvar expr arr = match expr with
      | Const'(s1)->          arr
      | Var'(VarFree v1) ->   arr@[v1]
      | Var'(v1) ->           arr
      | Box'(v1)->            arr
      | BoxGet'(v1)->         arr
      | BoxSet'(v1,e1) ->     (fvar e1 arr)
      | If'(t1, th1, el1)->   (fvar t1 arr) @ (fvar th1 []) @ (fvar el1 [])
      | Seq'(l1) ->
                              let apply_fvar_with_map single = fvar single [] in
                              let map_seq = List.map apply_fvar_with_map l1 in
                              let flattened = (map_flatten_func map_seq []) in
                              arr@flattened
      | Or'(l1) ->
                              let apply_fvar_with_map single = fvar single [] in
                              let map_or = List.map apply_fvar_with_map l1 in
                              let flattened = (map_flatten_func map_or []) in
                              arr@flattened
      | Set'(var, val1) ->     (fvar val1 arr)
      | Def'(VarFree v1, val1)->      (fvar val1 arr@[v1])
      | Def'(v1, val1)->      raise X_define_param_bound_in_fvar_tbl
      | LambdaSimple'(vars, body)->
                              (fvar body arr)
      | LambdaOpt'(vars, var, body) ->
                              (fvar body arr)
      | Applic'(proc, args) ->
                              let apply_fvar_with_map single = fvar single [] in
                              let map_args = List.map apply_fvar_with_map args in
                              let flattened = (map_flatten_func map_args []) in
                              (fvar proc arr) @ flattened
      | ApplicTP'(proc, args) ->
                              let apply_fvar_with_map single = fvar single [] in
                              let map_args = List.map apply_fvar_with_map args in
                              let flattened = (map_flatten_func map_args []) in
                              (fvar proc arr) @ flattened
      (* | _ -> raise X_procces_const *)
      in 
      fvar expr [];;


  let allocate_mem_fvar_func arr_without_dups = 
    let rec allocate_mem arr res index = match arr with
    | [] -> res
    | _ ->  
            let head = (List.hd arr) in
            let tail = (List.tl arr) in 
            caten_head head tail res index
  
    and caten_head hd arr res index = (allocate_mem arr (res@[(hd, (index * 8))]) (index + 1))
    in
    allocate_mem arr_without_dups [] 0 ;;


    let primitive_names_to_labels =
      [
        (* Type queries  *)
        "boolean?", "boolean?"; "flonum?", "flonum?"; "rational?", "rational?";
        "pair?", "pair?"; "null?", "null?"; "char?", "char?"; "string?", "string?";
        "procedure?", "procedure?"; "symbol?", "symbol?";
        (* String procedures *)
        "string-length", "string_length"; "string-ref", "string_ref"; "string-set!", "string_set";
        "make-string", "make_string"; "symbol->string", "symbol_to_string";
        (* Type conversions *)
        "char->integer", "char_to_integer"; "integer->char", "integer_to_char"; "exact->inexact", "exact_to_inexact";
        (* Identity test *)
        "eq?", "eq?";
        (* Arithmetic ops *)
        "+", "add"; "*", "mul"; "/", "div"; "=", "eq"; "<", "lt";
        (* Additional rational numebr ops *)
        "numerator", "numerator"; "denominator", "denominator"; "gcd", "gcd";
        (* you can add yours here *)
        "apply", "apply";
         "car", "car";
         "cdr", "cdr"; 
         "cons", "cons";
         "set-car!", "set_car";
         "set-cdr!", "set_cdr";  
      ] ;;

      
  
    let prims_to_fvar_func (prim, label) = prim;;
    let add_prims_to_fvar_tbl = List.map prims_to_fvar_func primitive_names_to_labels;;
    let make_fvars_tbl asts =  (allocate_mem_fvar_func (remove_duplicates_func (add_prims_to_fvar_tbl @ (map_flatten_func  (List.map procces_fvar asts) [])) ));;
    (* let make_fvars_tbl asts=  (allocate_mem_fvar_func (remove_duplicates_func (add_prims_to_fvar_tbl@( map_flatten_func  (List.map procces_fvar asts) [])) ));; *)






  (* let make_fvars_tbl asts = raise X_not_yet_implemented;; *)
  (* let generate consts fvars e = raise X_not_yet_implemented;; *)






    

  let generate_helper consts fvars e =

    let rec generate_func consts fvars e index env_num father_varlen = match e with
    | Const'(s1)->          String.concat "" ["mov rax, const_tbl+"; (return_address_in_const_table_func consts s1);"\n"]
    | Var'(VarParam(var_name,minor)) -> 
                            String.concat "" ["mov rax, qword [rbp + ";(string_of_int (8 * (4 + minor)));"]\n"]
    | Var'(VarBound (v1,major,minor))->
                            String.concat "" ["mov rax, qword [rbp + 16]\n"; 
                                              "mov rax, qword [rax + "; (string_of_int (8*major));"]\n";
                                              "mov rax, qword [rax + "; (string_of_int (8*minor));"]\n"]
                            
    | Var'(VarFree v1) ->   
                            let labelInFVarTable = return_index_in_fvar_table_func fvars v1 in
                            (* String.concat "" ["mov rax, qword [ fvar_tbl + (";(labelInFVarTable);" * WORD_SIZE)]\n"] *)
                            String.concat "" ["mov rax, qword [ fvar_tbl + ";(labelInFVarTable);"]\n"]
    
    | Box'(v1)->            String.concat "" [generate_func consts fvars (Var'(v1)) index env_num father_varlen;
                                              "MALLOC rcx, WORD_SIZE\n";
                                              "mov qword [rcx], rax\n";
                                              "mov rax, rcx\n"]

    | BoxGet'(v1)->         String.concat "" [generate_func consts fvars (Var'(v1)) index env_num father_varlen;
                                              "mov rax, qword [rax]\n"]
                                              
    | BoxSet'(v1,e1) ->     String.concat "" [generate_func consts fvars e1 index env_num father_varlen;
                                              "push rax\n";
                                              generate_func consts fvars (Var'(v1)) index env_num father_varlen;
                                              "pop qword [rax]\n";
                                              "mov rax, SOB_VOID_ADDRESS\n"]
   
    | If'(t1, th1, el1)->   
                            (* let updated_index = (index + 1) in *)
                            let updated_index = index in
                            let a = (ref updated_index) in
                            let address = 2*(Obj.magic a) in

                            String.concat "" [generate_func consts fvars t1 updated_index env_num father_varlen;
                                              "cmp rax, SOB_FALSE_ADDRESS\n";
                                              "je Lelse";  (string_of_int address); "\n";
                                              generate_func consts fvars th1 updated_index env_num father_varlen;
                                              "jmp Lexit";(string_of_int address);"\n";
                                              "Lelse"; (string_of_int address); ":\n";
                                              generate_func consts fvars el1 updated_index env_num father_varlen;
                                              "Lexit"; (string_of_int address); ":\n";]


    | Seq'(e_lst) ->        (generate_seq consts fvars e_lst "" index env_num father_varlen)
    | Or'(or_lst) ->
                            let a = (ref index) in
                            let address = 2*(Obj.magic a) in
                            (generate_or consts fvars or_lst "" (index + 1) env_num father_varlen address)
    | Set'(VarParam(var_name,minor), c) -> 
                            String.concat "" [(generate_func consts fvars c index env_num father_varlen); "\n";
                            "mov qword [rbp + ";(string_of_int (8 * (4 + minor))); "],rax\n";
                            "mov rax, SOB_VOID_ADDRESS\n"]
    | Set'(VarBound (v1,major,minor), c) -> 
                            String.concat "" [(generate_func consts fvars c index env_num father_varlen); "\n";
                            "mov rbx, qword [rbp + 16]\n";
                            "mov rbx, qword [rbx + "; (string_of_int (8*major));"]\n";
                            "mov qword [rbx + "; (string_of_int (8*minor));"], rax\n";
                            "mov rax, SOB_VOID_ADDRESS\n"]
    | Set'(VarFree v1, c) -> 
                            define_exp_set_fvar consts fvars v1 c index env_num father_varlen

    | Def'(VarFree v1, val1)->
                            define_exp_set_fvar consts fvars v1 val1 index env_num father_varlen
                            
    
    | LambdaSimple'(vars, body)-> generate_lambda_simple consts fvars vars body (index + 1) (env_num +1) father_varlen
                            
    | LambdaOpt'(vars, variadic, body) -> generate_lambda_opt consts fvars vars variadic body (index + 1) (env_num +1) father_varlen
                            
    | Applic'(proc, args) -> 
                            (applics consts fvars proc args index env_num father_varlen)
                            
    | ApplicTP'(proc, args) -> 
                            (applicTP_foo consts fvars proc args index env_num father_varlen)
                            
    | _ -> raise X_generate
    



    (* and generate_with_parenthesis consts fvars e = String.concat "" ["[";generate_func consts fvars e;"]"] *)

    and generate_seq consts fvars e_lst res index env_num father_varlen= match e_lst with
    | [] -> res
    | _ ->  generate_seq consts fvars (List.tl e_lst) (String.concat "" [res; generate_func consts fvars (List.hd e_lst) index env_num father_varlen]) index env_num father_varlen


    and generate_or consts fvars e_lst res index env_num father_varlen address =
    (* let a = (ref index) in
    let address = 2*(Obj.magic a) in *)
    match e_lst with
    | [] ->
                            (* let a = (ref index) in
                            let address = 2*(Obj.magic a) in *)
                            (String.concat "" [res;"Lexitor";(string_of_int address); ":\n" ])
    | _ ->
                            (* let a = (ref index) in
                            let address = 2*(Obj.magic a) in *)
                            generate_or consts fvars (List.tl e_lst) (String.concat "" [res; generate_func consts fvars (List.hd e_lst) index env_num father_varlen;
                                                                         "cmp rax, SOB_FALSE_ADDRESS\n";
                                                                         "jne Lexitor";(string_of_int address); "\n"]) index env_num father_varlen address

    and push_applic_args consts fvars app_lst res index env_num father_varlen= match app_lst with
    | [] -> res
    | _ ->  (push_applic_args consts fvars (List.tl app_lst) (String.concat "" [res; generate_func consts fvars (List.hd app_lst) index env_num father_varlen;
                                                                                "push rax\n"]) index env_num father_varlen)
    
    and applics consts fvars proc args index env_num father_varlen=
        let num_args = (List.length args) in
        let reversed_args = List.rev args in
        let push_args = push_applic_args consts fvars reversed_args "" index env_num father_varlen in

        let push_n = (String.concat "" [push_args; "push "; (string_of_int num_args); "\n" ;
                                        (generate_func consts fvars proc index env_num father_varlen);
                                        (* "push rax→ env"; *)
                                        "CLOSURE_ENV rbx, rax\n";
                                        "push rbx\n";
                                        (* "call rax→ code"; *)
                                        "CLOSURE_CODE rbx, rax\n";

                                        (* check and put args num on rdi *)
                                        (* "mov rdi, "; (string_of_int num_args); "\n"; *)

                                        "call rbx\n";
                                        (* " SLIDE 96"  *)
                                        "add rsp, 8*1 ; pop env\n";
                                        "pop rbx ; pop arg count\n";
                                        "shl rbx, 3 ; rbx = rbx * 8\n";
                                        "add rsp , rbx; pop args\n"])
        in push_n

    (* and move_and_pop_stack_frame_TP father_varlen num_args = 
        let space3_plusN = (4 + father_varlen) in
        let rec move_pop res father_cells_remain my_cells_remain index =
          if (my_cells_remain > 0) 
          then 
              (move_pop (String.concat "" [res; "mov rcx, qword [rbp - "; (string_of_int (8 * (index+1) ) ); "]\n ";
                                                "mov qword [rbp + "; (string_of_int (8 * (space3_plusN - index) ) ); "] , rcx\n " ])  (father_cells_remain - 1) (my_cells_remain - 1) (index+1))
          else if(father_cells_remain >= 0) 
          then
          (move_pop (String.concat "" [res; "pop rcx\n ";])  (father_cells_remain - 1) (my_cells_remain - 1) (index+1))
          else res

        in (move_pop "" space3_plusN num_args 0) *)

    and applicTP_foo consts fvars proc args index env_num father_varlen=
        let num_args = (List.length args) in
        let reversed_args = List.rev args in
        let push_args = push_applic_args consts fvars reversed_args "" index env_num father_varlen in
        let push_n = (String.concat "" [push_args; "push "; (string_of_int num_args); "\n" ;
                                        (generate_func consts fvars proc index env_num father_varlen);
                                        (* "push rax→ env"; *)
                                        "CLOSURE_ENV rbx, rax\n";
                                        "push rbx\n";
                                        (* old ret addr *)
                                        "push qword [rbp + 8 * 1] ; old ret addr\n";
                                        (* "jmp rax→ code"; *)
                                        "CLOSURE_CODE rbx, rax\n      ;move_and_pop_stack_frame_TP\n";
                                        (* fix the stack *)
                                        "mov r8, qword [rbp]\n ";
                                        (* "mov r8, rbp\n "; *)

                                        "mov rcx,0\n  ;clean stack if there is difference of args. rcx = 4+args rcx *8\n";
                                        "mov rcx, PARAM_COUNT ;PARAM_COUNT of father frame\n";
                                        "add rcx, 4\n  ;(not TODO) 4 cells if not magic , 5 if use of magic\n";
                                        
                                        "SHIFT_FRAME " ; (string_of_int (4+num_args)) ;"\n";

                                        (* "mov ecx, " ; (string_of_int (4+num_args)) ;"\n";
                                        "SHIFT_FRAME ecx \n"; *)
                                        (* (move_and_pop_stack_frame_TP father_varlen num_args); *)
                                        "shl rcx , 3\n  ;clean stack if there is difference of args. rcx = 4+args rcx *8\n";
                                        "add rsp,rcx\n";
                                        (* " SLIDE 107"  *)

                                        (* check and put args num on rdi *)
                                        (* "mov rdi, "; (string_of_int num_args); "\n"; *)
                                        "mov rbp, r8\n ";
                                        "jmp rbx\n";
                                        ])
        in push_n

    and define_exp_set_fvar consts fvars v c index env_num father_varlen= 
                            let labelInFVarTable = return_index_in_fvar_table_func fvars v in

                            let returned = String.concat "" [(generate_func consts fvars c index env_num father_varlen);
                            (* "mov qword [ fvar_tbl + (";labelInFVarTable;" * WORD_SIZE)], rax\n"; *)
                            "mov qword [ fvar_tbl + ";labelInFVarTable;"], rax\n";
                            "mov rax, SOB_VOID_ADDRESS\n"]

                            in returned




    and generate_lambda_simple consts fvars vars body lbl_index env_num father_varlen=
      
      (* magically generate an unique lbl_index based on the ref label we convert the addres from int ref to int with magic *)
      let a = (ref lbl_index) in
      let address = 2*(Obj.magic a) in
      (* Printf.printf "%d" address;; *)

      let lambda_code = String.concat "" ["jmp Lcont"; (string_of_int address);"\n";
                                          "Lcode"; (string_of_int address); ":\n";
                                              "push rbp\n";
                                              "mov rbp , rsp\n";
                                              (* ";ref fuck you "; (string_of_int address) ;"\n"; *)
                                              (generate_func consts fvars body lbl_index env_num (List.length vars));
                                              "leave\n";
                                              "ret\n";
                                          "Lcont"; (string_of_int address); ":\n"] in

      let prev_lex_env = "\n\nmov rcx, qword [rbp + WORD_SIZE * 2] ;get previous env\n" in
      let alloc_ext_env = String.concat "" ["mov rax, WORD_SIZE *";  (string_of_int env_num) ;" ;size of ext env\n";
                                      "MALLOC rbx, rax ;malloc vector for ext env \n";] in
      (* copy the prev_env with offset of size 1, and stop when env ==0 *)
      let rec loop_copy_env res loop_index prev_env_size  = 
        if (loop_index < prev_env_size) 
        then 
            (loop_copy_env (String.concat "" [res; "mov rdx, qword [rcx + WORD_SIZE *"; (string_of_int loop_index); "] ;loop_copy_env\n";
                                                   "mov qword [rbx + WORD_SIZE *"; (string_of_int (loop_index + 1)); "], rdx ;loop_copy_env\n" ]) (loop_index + 1) prev_env_size ) 
        else res
      in
      let ext_env_copy = loop_copy_env "" 0 env_num in
      
      let alloc_vars_vetor = String.concat "" ["mov rax, WORD_SIZE *"; (string_of_int father_varlen);" ;size of new major 0 vars\n";
                                              "MALLOC rcx, rax ;malloc vector major 0 vars\n";]
      in

      let rec loop_copy_vars_from_stack res loop_index varlen  = 
        if (loop_index < varlen) 
        then 
            (loop_copy_vars_from_stack (String.concat "" [res; "mov rdx, qword [rbp + "; (string_of_int (8*(loop_index + 4))); "] ;loop_copy_vars_from_stack\n";
                                                   "mov qword [rcx + "; (string_of_int (8*loop_index)); "], rdx ;loop_copy_vars_from_stack\n" ]) (loop_index + 1) varlen ) 
        else res
      in
      let ext_env_from_stack = loop_copy_vars_from_stack "" 0 father_varlen in
      let params = "mov qword [rbx + 0] , rcx\n" in

      let finish = if(env_num == 0)
                      then                  
                        (String.concat "" ["MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, Lcode"^ (string_of_int address)  ^ ")\n" ; lambda_code])
                    else if (env_num == 1)
                      then
                    (* there is no env to copy so no ext_env_copy when env_num == 1 *)
                        (String.concat "" [prev_lex_env; alloc_ext_env; alloc_vars_vetor; ext_env_from_stack;params;
                                          "MAKE_CLOSURE(rax, rbx, Lcode"^ (string_of_int address)  ^ ")\n" ; lambda_code])
                    else
                        (String.concat "" [prev_lex_env; alloc_ext_env; ext_env_copy; alloc_vars_vetor; ext_env_from_stack;params;
                                          "MAKE_CLOSURE(rax, rbx, Lcode"^ (string_of_int address)  ^ ")\n" ; lambda_code])
      in
      finish


      and generate_lambda_opt consts fvars vars variadic body lbl_index env_num father_varlen =
        (* magically generate an unique lbl_index based on the ref label we convert the addres from int ref to int with magic *)
        let a = (ref lbl_index) in
        let address = 2*(Obj.magic a) in
        (* Printf.printf "%d" address;; *)
        
        let adjust_the_stack_for_the_optional = String.concat "" [
                            "mov rbx, PARAM_COUNT_OPT_RSP   ;params\n";
                            "cmp rbx, "; (string_of_int ((List.length vars)+1)); "\n";
                            (* "cmp rdi, "; (string_of_int (List.length vars)); "\n"; *)

                            "jl LnoVariadic"; (string_of_int address) ; "\n";
                             
                            ";OPT ,yesVariadic, execute this lines if lambda applied NOT on exect number of params\n";
                            "mov rcx, PARAM_COUNT_OPT_RSP\n"; (*6*)
                            (* check this 6-3 or 6-3+1?*)
                            "sub rcx, "; (string_of_int (List.length vars)) ;" ; rcx contains the length of varicadic\n"; (*6-3vars = 3variadic*)
                            (* check this *)
                            "mov rsi,rcx\n";
                            "CREATE_VARIADIC_OPT_LIST rsi\n";
                            
                            "mov rdx, "; (string_of_int ((List.length vars)+1)) ;" ; rdx contains the length of vars plus 1 (vars +variadic len)\n"; (*4*)
                            "mov PARAM_COUNT_OPT_RSP, rdx       ;update num args\n";
                            
                            "dec rcx      ;num of cells shifts up\n"; (*2*)
                            "mov rsi,rcx\n";
                            "LAMBDA_OPT_SHIFT_FRAME_UP rsi ;rsi is the number of shift requiered \n"; (*6-4 =2*)

                            (* pop rcx times by fixing rsp*)
                            "shl rcx , 3  ;clean stack if there is difference of args. rcx = PARAM_COUNT_OPT_RSP-(1+vars)\n";
                            "add rsp,rcx\n";
                            
                             ";for commit\n";

                            "jmp Optcont"; (string_of_int address) ; "\n";
                            
                            "LnoVariadic"; (string_of_int address) ; ":\n";
                            (* "mov r9, "; (string_of_int ((List.length vars) + 2))  ;"\n"; *)
                            (* "SHIFT_FRAME_DOWN_BY_ONE_CELL r9  ; go 0 to n times include.. so n+1 times\n"; *)
                            "SHIFT_FRAME_DOWN_BY_ONE_CELL "; (string_of_int ((List.length vars) + 3)) ;"      ; vars+3 times\n";
                            (* "sub rsp,WORD_SIZE    ;tell the stack that we are down by one cell\n"; *)

                            (* "inc rcx\n"; *)
                            (* "mov PARAM_COUNT_OPT , rcx\n"; *)

                            "Optcont"; (string_of_int address) ; ":\n";
                            ]
        in
        

        let lambda_code =
          let new_father_var_len = ((List.length vars) + 1)
          in
          String.concat "" ["jmp Lcont"; (string_of_int address);"\n";
                                            "Lcode"; (string_of_int address); ":\n";

                                                (* test *)
                                                (* "push rbp\n";
                                                "mov rbp , rsp\n"; *)
                                                
                                                adjust_the_stack_for_the_optional ;
                                                (* "pop rbp\n"; *)

                                                "push rbp\n"; 
                                                "mov rbp , rsp\n"; 
                                                (* ";ref you "; (string_of_int address) ;"\n"; *)
                                                (* father_varlen must add 1 to the vars *)
                                                (generate_func consts fvars body lbl_index env_num new_father_var_len);
                                                
                                                "leave\n";
                                                "ret\n";
                                            "Lcont"; (string_of_int address); ":\n"] in

        let prev_lex_env = "\n\nmov rcx, qword [rbp + WORD_SIZE * 2] ;get previous env\n" in
        let alloc_ext_env = String.concat "" ["mov rax, WORD_SIZE *";  (string_of_int env_num) ;" ;size of ext env\n";
                                        "MALLOC rbx, rax ;malloc vector for ext env \n";] in
        (* copy the prev_env with offset of size 1, and stop when env ==0 *)
        let rec loop_copy_env res loop_index prev_env_size  = 
          if (loop_index < prev_env_size) 
          then 
              (loop_copy_env (String.concat "" [res; "mov rdx, qword [rcx + WORD_SIZE *"; (string_of_int loop_index); "] ;loop_copy_env\n";
                                                    "mov qword [rbx + WORD_SIZE *"; (string_of_int (loop_index + 1)); "], rdx ;loop_copy_env\n" ]) (loop_index + 1) prev_env_size ) 
          else res
        in
        let ext_env_copy = loop_copy_env "" 0 env_num in
        
        let alloc_vars_vetor = String.concat "" ["mov rax, WORD_SIZE *"; (string_of_int father_varlen);" ;size of new major 0 vars\n";
                                                "MALLOC rcx, rax ;malloc vector major 0 vars\n";]
        in

        let rec loop_copy_vars_from_stack res loop_index varlen  = 
          if (loop_index < varlen) 
          then 
              (loop_copy_vars_from_stack (String.concat "" [res; "mov rdx, qword [rbp + "; (string_of_int (8*(loop_index + 4))); "] ;loop_copy_vars_from_stack\n";
                                                    "mov qword [rcx + "; (string_of_int (8*loop_index)); "], rdx ;loop_copy_vars_from_stack\n" ]) (loop_index + 1) varlen ) 
          else res
        in
        let ext_env_from_stack = loop_copy_vars_from_stack "" 0 father_varlen in
        let params = "mov qword [rbx + 0] , rcx\n" in

        let finish = if(env_num == 0)
                        then                  
                          (String.concat "" ["MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, Lcode"^ (string_of_int address)  ^ ")\n" ; lambda_code])
                      else if (env_num == 1)
                        then
                      (* there is no env to copy so no ext_env_copy when env_num == 1 *)
                          (String.concat "" [prev_lex_env; alloc_ext_env; alloc_vars_vetor; ext_env_from_stack;params;
                                            "MAKE_CLOSURE(rax, rbx, Lcode"^ (string_of_int address)  ^ ")\n" ; lambda_code])
                      else
                          (String.concat "" [prev_lex_env; alloc_ext_env; ext_env_copy; alloc_vars_vetor; ext_env_from_stack;params;
                                            "MAKE_CLOSURE(rax, rbx, Lcode"^ (string_of_int address)  ^ ")\n" ; lambda_code])
        in
        finish
      






    in
    generate_func consts fvars e 0 (-1) 0;;


    
  let generate consts fvars e = generate_helper consts fvars e;;



  let run_gen expr_lst =
    let constable = make_consts_tbl expr_lst in
    let fvar_table = make_fvars_tbl expr_lst in
    generate_helper constable fvar_table (List.hd expr_lst);;
    

    let one_to_three s = List.map Semantics.run_semantics
    (Tag_Parser.tag_parse_expressions
       (Reader.read_sexprs s));;


end;;
open Code_Gen;;
(* 
 
one_to_three "((lambda (x . y)
     ((lambda ()
        (set-cdr! x y)))
     x)
   (cons 1 2))";;
- : expr' list =

[Applic'
  (LambdaOpt' (["x"], "y",
    Seq'
     [Applic'
       (LambdaSimple' ([],
         ApplicTP' (Var' (VarFree "set-cdr!"),
          [Var' (VarBound ("x", 0, 0)); Var' (VarBound ("y", 0, 1))])),
       []);
      Var' (VarParam ("x", 0))]),
  [Applic' (Var' (VarFree "cons"),
    [Const' (Sexpr (Number (Fraction (1, 1))));
     Const' (Sexpr (Number (Fraction (2, 1))))])])]


 


 one_to_three "((lambda (x . y)
     
        (set-cdr! x y)
     x)
   (cons 1 2))
";;
- : expr' list =
[Applic'
  (LambdaOpt' (["x"], "y",
    Seq'
     [Applic' (Var' (VarFree "set-cdr!"),
       [Var' (VarParam ("x", 0)); Var' (VarParam ("y", 1))]);
      Var' (VarParam ("x", 0))]),
  [Applic' (Var' (VarFree "cons"),
    [Const' (Sexpr (Number (Fraction (1, 1))));
     Const' (Sexpr (Number (Fraction (2, 1))))])])]
 
 
(
  (lambda (x . y)
     ((lambda ()
        (set-cdr! x y)))
                                    x)
   (cons 1 2)) *)

   