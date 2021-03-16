(* pc.ml
 * A parsing-combinators package for ocaml
 *
 * Prorammer: Mayer Goldberg, 2018
 *)

(* general list-processing procedures *)


(*
e = expression
es = expressions
s = string
f = function
nt = non terminal
ch = char
ci = case insensitive
*)

let rec ormap f s =
  match s with
  | [] -> false
  | car :: cdr -> (f car) || (ormap f cdr);;

let rec andmap f s =
  match s with
  | [] -> true
  | car :: cdr -> (f car) && (andmap f cdr);;	  

let lowercase_ascii  =
  let delta = int_of_char 'A' - int_of_char 'a' in
  fun ch ->
  if ('A' <= ch && ch <= 'Z')
  then char_of_int ((int_of_char ch) - delta)
  else ch;;

let string_to_list str =
  let rec loop i limit =
    if i = limit then []
    else (String.get str i) :: (loop (i + 1) limit)
  in
  loop 0 (String.length str);;

let list_to_string s =
  String.concat "" (List.map (fun ch -> String.make 1 ch) s);;

module PC = struct

(* the parsing combinators defined here *)
  
exception X_not_yet_implemented;;

exception X_no_match;;

let const pred =
  function 
  | [] -> ra  ise X_no_match
  | e :: s ->
     if (pred e) then (e, s)
     else raise X_no_match;;

     (*The caten combinator essentially takes two functions (since parsers created using
PC are functions), and constructs a new function (i.e. parser). The caten function
adds the control flow that sends the input into the first parser, and then sends the
remaining list of that first parser to the second parser.
The caten operator produces tuples, the type of the tuple elements depends 
on the packing of the underlying parsers.*)

let caten nt1 nt2 s =
  let (e1, s) = (nt1 s) in
  let (e2, s) = (nt2 s) in
  ((e1, e2), s);;

  (*we use the pack combinator to transform the accepted tokens (characters) 
  into an internal representation used in our parse tree.
   we give the combinator pack two arguments : the first
one is a parser , and the second is function to process the result of parsing ( Lets call it func_proc ). 
The output of our parses is the following
(parsing_result, list_of_remaining_chars). So what actually pack do is
(func_proc(parsing_result), list_of_remaining_chars) , applies func_proc
to parsing_result .*)

let pack nt f s =
  let (e, s) = (nt s) in
  ((f e), s);;

  (*parser that reads nothing.
  we use it in cases where we use abstract combinator that expect 2 parser, but we parse nothing on the left,
  so we use it as a dummy place holder *))
let nt_epsilon s = ([], s);;

let caten_list nts =
  List.fold_right
    (fun nt1 nt2 ->
     pack (caten nt1 nt2)
	  (fun (e, es) -> (e :: es)))
    nts
    nt_epsilon;;

    (*The disj combinator (which implements disjunction) takes two
functions, and constructs a sort of ”or” statement between them, where if the first
parser rejects the input (i.e. raises X_no_match) the input is then sent to the second
parser instead.*)

let disj nt1 nt2 =
  fun s ->
  try (nt1 s)
  with X_no_match -> (nt2 s);;

let nt_none _ = raise X_no_match;;
  
let disj_list nts = List.fold_right disj nts nt_none;;

let delayed thunk s =
  thunk() s;;

let nt_end_of_input = function
  | []  -> ([], [])
  | _ -> raise X_no_match;;

  (*takes a parser and a string, and parses the strin zero or more time as long as it can parse*)
let rec star nt s =
  try let (e, s) = (nt s) in
      let (es, s) = (star nt s) in
      (e :: es, s)
  with X_no_match -> ([], s);;

let plus nt =
  pack (caten nt (star nt))
       (fun (e, es) -> (e :: es));;

(* takes nt and pred (predicate) and returns a parser.
The parser parse the string only if pred(s) = true.
we first define result to be (e ,s) as if nt did parse s.
onlt then, wh check if we get true from pred (e), and if we do we return the (e, s) = result we parsed before.
else, if pred (e) = false, we return x_no_match.
 *)

let guard nt pred s =
  let ((e, _) as result) = (nt s) in
  if (pred e) then result
  else raise X_no_match;;
  
let diff nt1 nt2 s =
  match (let result = nt1 s in
	 try let _ = nt2 s in
	     None
	 with X_no_match -> Some(result)) with
  | None -> raise X_no_match
  | Some(result) -> result;;

let not_followed_by nt1 nt2 s =
  match (let ((_, s) as result) = (nt1 s) in
	 try let _ = (nt2 s) in
	     None
	 with X_no_match -> (Some(result))) with
  | None -> raise X_no_match
  | Some(result) -> result;;
    
  
(*takes a nt and returns a parser "fun s" = "lambda s".
the function is taking the string s and try to parse it with nt. 
If succeed, returns (Some (e), s) = the e that was parsed and the remained string s.
else, returns (None, s)  = the string remains as it was.
So we are promised to get back something like (Some e, s) or (None, s) - which is better than "X_no_macth".

*))  
let maybe nt s =
  try let (e, s) = (nt s) in
      (Some(e), s)
  with X_no_match -> (None, s);;

(* useful general parsers for working with text 

The char parser-constructor takes a single character, C, and returns a parser (i.e.
function) which takes a list of character and returns a pair. That pair is composed
of the first character of the list, if it’s C, and the rest of the list. So for example:
    # let _a_ = (char 'a');;
    # _a_ (string_to_list "abc");;
    - : char * char list = ('a', ['b'; 'c'])
If the first char on the list is not C, the parser will raise an X_no_match exception.*)


(* takes equal=predicate, and ch1 (some char),
and returns parser that checks if ch1 and ch2 are "equals"
 (the predicate equal returns true when given ch1 an ch2).
*)
let make_char equal ch1 = const (fun ch2 -> equal ch1 ch2);;

(*the difference between char and char_ci is a different predicate given to make_char (case sensitive or insensitive*)
let char = make_char (fun ch1 ch2 -> ch1 = ch2);;

(*takes 2 chars, make them lower case, and only then compare them using "="*)
let char_ci =
  make_char (fun ch1 ch2 ->
	     (lowercase_ascii ch1) =
         (lowercase_ascii ch2));;
         
(*builds a parser that "recognize" the gicen word "str"*))
let make_word char str = 
  List.fold_right
    (fun nt1 nt2 -> pack (caten nt1 nt2) (fun (a, b) -> a :: b))
    (List.map char (string_to_list str))   (*takes the str, make it a list of chars (["s";"t";"r"]), and than performs "char"
                                           (builds a parser that parses the specific char) on every char of the list(that's the "map" part),
                                           so we get a list of parsers *))
    nt_epsilon;;

(*word - pareses a given word with case sensitive,
  word_ci = parses a given wors with case INsensitive.
 we make this different by giving make word different parsers (char or char_ci)*))
let word = make_word char;;

let word_ci = make_word char_ci;;


(*builds a parser than parse a group of chars.
for example:
  one_of "abc"
will return a parser that parses the letters "a", "b" or "c" *))
let make_one_of char str =
  List.fold_right
    disj
    (List.map char (string_to_list str))
    nt_none;;
(*builds a case sensitive parser using make_one_of*))
let one_of = make_one_of char;;
(*builds a case INsensitive parser using make_one_of*))
let one_of_ci = make_one_of char_ci;;

let nt_whitespace = const (fun ch -> ch <= ' ');;

(*builds a parser than parse a group of chars in a given range.
for example:
  range 'a' 'k'
will return a parser that parses the letters 'a','b','c'...'k' *))
let make_range leq ch1 ch2 (s : char list) =
  const (fun ch -> (leq ch1 ch) && (leq ch ch2)) s;; (*leq = less or equal. basically it says (ch1 <= ch) && (ch <= ch2)*))
(*builds a case sensitive parser using make_range*))
let range = make_range (fun ch1 ch2 -> ch1 <= ch2);;
(*builds a case INsensitive parser using make_range*))
let range_ci =
  make_range (fun ch1 ch2 ->
	      (lowercase_ascii ch1) <=
		(lowercase_ascii ch2));;

let nt_any (s : char list) = const (fun ch -> true) s;;

(*This function helps to debug our parser. it allows as to get informative errors, rather then "x_no_match".
it takes documentation string and a parser (and optionally a word we check), and returns a tracing parser.
for example:
  test_string (trace_pc "the word \"hi\"" (word "hi")) "high"
returns 
;;; The word "hi" matched the head of "high",
    and the remaining string is "gh"
- : char 1list * string = (['h': 'i'], "=>[gh]")
 *))
let trace_pc desc nt s =
  try let ((e, s') as args) = (nt s)
      in
      (Printf.printf ";;; %s matched the head of \"%s\", and the remaining string is \"%s\"\n"
		     desc
		     (list_to_string s)
		     (list_to_string s') ;
       args)
  with X_no_match ->
    (Printf.printf ";;; %s failed on \"%s\"\n"
		   desc
		   (list_to_string s) ;
     raise X_no_match);;

(* testing the parsers *)

let test_string nt str =
  let (e, s) = (nt (string_to_list str)) in
  (e, (Printf.sprintf "->[%s]" (list_to_string s)));;

end;; (* end of struct PC *)

(* end-of-input *)
