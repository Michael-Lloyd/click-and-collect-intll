(* DEFINITION OF LINEAR LOGIC FORMULAS AND SEQUENTS *)

(* The core data structure representing Linear Logic formulas.
   Linear Logic is a resource-sensitive logic where each formula must be used exactly once.
   
   The formula constructors represent:
   - One: multiplicative unit (⊤ in multiplicative context)
   - Bottom: multiplicative zero (⊥ in multiplicative context) 
   - Top: additive unit (⊤ in additive context)
   - Zero: additive zero (0 in additive context)
   - Litt: atomic proposition (literal like A, B, C)
   - Dual: orthogonal/negation of a literal (A^, B^, etc.)
   - Tensor: multiplicative conjunction (A ⊗ B) - "both A and B"
   - Par: multiplicative disjunction (A ⅋ B) - "A or B, but resources split"
   - With: additive conjunction (A & B) - "both A and B, choose context"
   - Plus: additive disjunction (A ⊕ B) - "A or B, choose one"
   - Ofcourse: exponential "of course" (!A) - "A available infinitely"
   - Whynot: exponential "why not" (?A) - "A available optionally"
*)
type formula =
  | One
  | Bottom
  | Top
  | Zero
  | Litt of string
  | Dual of string
  | Tensor of formula * formula
  | Par of formula * formula
  | With of formula * formula
  | Plus of formula * formula
  | Ofcourse of formula
  | Whynot of formula;;

(* A sequent is a list of formulas representing a judgment in sequent calculus.
   In Linear Logic, a sequent Γ ⊢ Δ represents "from context Γ, we can derive Δ".
   Here we represent it as a single list where formulas before ⊢ are negated.
*)
type sequent = formula list;;


(* CORE OPERATIONS ON FORMULAS AND SEQUENTS *)

(* Convert a sequent (list of formulas) to a single formula using Par.
   Empty sequent becomes Bottom (false), single formula stays as-is,
   multiple formulas are combined with Par (multiplicative disjunction).
   This reflects that a sequent A,B,C is equivalent to A ⅋ B ⅋ C.
*)
let rec sequent_to_formula = function
  | [] -> Bottom
  | [f] -> f
  | f1 :: f2 :: context -> sequent_to_formula (Par (f1, f2) :: context)

(* Compute the dual (orthogonal/negation) of a formula.
   In Linear Logic, every formula has a dual such that A ⊢ B is equivalent to ⊢ A^, B.
   The duality relationships are:
   - Constants: 1^ = ⊥, ⊥^ = 1, ⊤^ = 0, 0^ = ⊤
   - Literals: A^ = A^, (A^)^ = A  
   - Connectives: (A⊗B)^ = A^ ⅋ B^, (A⅋B)^ = A^ ⊗ B^, etc.
   - Exponentials: (!A)^ = ?(A^), (?A)^ = !(A^)
*)
let rec dual =
    function
    | One -> Bottom
    | Bottom -> One
    | Top -> Zero
    | Zero -> Top
    | Litt x -> Dual x
    | Dual x -> Litt x
    | Tensor (e1, e2) -> Par (dual e1, dual e2)
    | Par (e1, e2) -> Tensor (dual e1, dual e2)
    | With (e1, e2) -> Plus (dual e1, dual e2)
    | Plus (e1, e2) -> With (dual e1, dual e2)
    | Ofcourse e -> Whynot (dual e)
    | Whynot e -> Ofcourse (dual e);;

(* Exception raised when trying to remove whynot from non-whynot formula *)
exception Not_whynot;;

(* Remove the whynot wrapper from all formulas in a list.
   Used in exponential rules where ?A becomes A.
   Raises Not_whynot if any formula is not wrapped in whynot.
*)
let rec remove_whynot = function
    | [] -> []
    | Whynot e :: l -> e :: remove_whynot l
    | _ -> raise Not_whynot;;

(* Add whynot wrapper to all formulas in a list.
   Used in exponential rules where A becomes ?A.
   This is needed for the promotion rule in Linear Logic.
*)
let rec add_whynot = function
    | [] -> []
    | e :: l -> Whynot e :: add_whynot l;;

(* Check if all formulas in a list are wrapped with whynot (?).
   This is required for certain exponential rules in Linear Logic.
   Empty list returns true (vacuously true).
*)
let rec has_whynot_context = function
    | [] -> true
    | Whynot _e :: tail -> has_whynot_context tail
    | _ -> false

(* Extract all variable names (literals) from a formula.
   Returns a list of all atomic proposition names appearing in the formula.
   Constants (One, Bottom, etc.) contribute no variable names.
   Both Litt and Dual contribute their underlying variable name.
*)
let rec get_variable_names =
    function
    | One -> []
    | Bottom -> []
    | Top -> []
    | Zero -> []
    | Litt x -> [x]
    | Dual x -> [x]
    | Tensor (e1, e2) -> get_variable_names e1 @ get_variable_names e2
    | Par (e1, e2) -> get_variable_names e1 @ get_variable_names e2
    | With (e1, e2) -> get_variable_names e1 @ get_variable_names e2
    | Plus (e1, e2) -> get_variable_names e1 @ get_variable_names e2
    | Ofcourse e -> get_variable_names e
    | Whynot e -> get_variable_names e;;

(* Get all unique variable names from a sequent, sorted alphabetically.
   Useful for analyzing what atomic propositions appear in a sequent.
*)
let get_unique_variable_names sequent =
    List.sort_uniq String.compare (List.concat_map get_variable_names sequent);;

let rec count_notation_in_formula notation_name = function
    | Litt x when x = notation_name -> 1
    | Dual x when x = notation_name -> 1
    | Tensor (e1, e2) | Par (e1, e2) | With (e1, e2) | Plus (e1, e2) ->
        count_notation_in_formula notation_name e1 + count_notation_in_formula notation_name e2
    | Ofcourse e | Whynot e -> count_notation_in_formula notation_name e
    | _ -> 0;;

let count_notation notation_name sequent =
    List.fold_right (fun f n -> count_notation_in_formula notation_name f + n) sequent 0

let sort sequent =
    List.sort compare sequent;;

let rec replace_in_formula alias formula = function
    | Litt s when s = alias -> formula
    | Dual s when s = alias -> dual formula
    | Tensor (e1, e2) -> Tensor (replace_in_formula alias formula e1, replace_in_formula alias formula e2)
    | Par (e1, e2) -> Par (replace_in_formula alias formula e1, replace_in_formula alias formula e2)
    | With (e1, e2) -> With (replace_in_formula alias formula e1, replace_in_formula alias formula e2)
    | Plus (e1, e2) -> Plus (replace_in_formula alias formula e1, replace_in_formula alias formula e2)
    | Ofcourse e -> Ofcourse (replace_in_formula alias formula e)
    | Whynot e -> Whynot (replace_in_formula alias formula e)
    | f -> f;;

let replace_in_sequent alias formula sequent =
     List.map (replace_in_formula alias formula) sequent;;

(* PATTERN MATCHING ON FORMULA *)

let is_top = function | Top -> true | _ -> false;;
let is_bottom = function | Bottom -> true | _ -> false;;
let is_par = function | Par _ -> true | _ -> false;;
let is_with = function | With _ -> true | _ -> false;;
let is_ofcourse = function | Ofcourse _ -> true | _ -> false;;


(* EXPORTS *)

type formula_format = {
    atom_preformat : string -> string;
    litt_format : (string -> string, unit, string) format;
    dual_format : (string -> string, unit, string) format;
    is_dual_atomic : bool;
    is_unary_atomic : bool;
    one_format : string;
    bottom_format : string;
    top_format : string;
    zero_format : string;
    tensor_format : (string -> string -> string, unit, string) format;
    par_format : (string -> string -> string, unit, string) format;
    with_format : (string -> string -> string, unit, string) format;
    plus_format : (string -> string -> string, unit, string) format;
    ofcourse_format : (string -> string, unit, string) format;
    whynot_format : (string -> string, unit, string) format }

let rec formula_export_atomic formatting =
  let unary_connective f e =
    let s, atomic = formula_export_atomic formatting e in
    let s_parenthesis = if atomic then s else "(" ^ s ^ ")" in
    Printf.sprintf f s_parenthesis, formatting.is_unary_atomic in
  let binary_connective f e1 e2 =
    let s1, atomic1 = formula_export_atomic formatting e1 in
    let s1_parenthesis = if atomic1 then s1 else "(" ^ s1 ^ ")" in
    let s2, atomic2 = formula_export_atomic formatting e2 in
    let s2_parenthesis = if atomic2 then s2 else "(" ^ s2 ^ ")" in
    Printf.sprintf f s1_parenthesis s2_parenthesis, false in
  function
  | One -> formatting.one_format, true
  | Bottom -> formatting.bottom_format, true
  | Top -> formatting.top_format, true
  | Zero -> formatting.zero_format, true
  | Litt x -> Printf.sprintf formatting.litt_format (formatting.atom_preformat x), true
  | Dual x -> Printf.sprintf formatting.dual_format (formatting.atom_preformat x), formatting.is_dual_atomic
  | Tensor (e1, e2) -> binary_connective formatting.tensor_format e1 e2
  | Par (e1, e2) -> binary_connective formatting.par_format e1 e2
  | With (e1, e2) -> binary_connective formatting.with_format e1 e2
  | Plus (e1, e2) -> binary_connective formatting.plus_format e1 e2
  | Ofcourse e -> unary_connective formatting.ofcourse_format e
  | Whynot e -> unary_connective formatting.whynot_format e


(* SEQUENT -> COQ *)

let coq_format = {
    atom_preformat = (fun x -> x);
    litt_format = "%s";
    dual_format = "dual %s";
    is_dual_atomic = false;
    is_unary_atomic = false;
    one_format = "one";
    bottom_format = "bot";
    top_format = "top";
    zero_format = "zero";
    tensor_format = "tens %s %s";
    par_format = "parr %s %s";
    with_format = "awith %s %s";
    plus_format = "aplus %s %s";
    ofcourse_format = "oc %s";
    whynot_format = "wn %s" }

let formula_to_coq formula =
  let s, _ = formula_export_atomic coq_format formula in s

let formula_list_to_coq formula_list =
    Printf.sprintf "[%s]" (String.concat "; " (List.map formula_to_coq formula_list));;

let sequent_to_coq sequent =
    Printf.sprintf "ll %s" (formula_list_to_coq sequent);;


(* SEQUENT -> LATEX *)

let litteral_to_latex s =
   (* Set numbers as indices. E.g.: A01' -> A_{01}' *)
    Str.global_replace (Str.regexp "\\([0-9]+\\)") "_{\\1}" s;;

let latex_format = {
    atom_preformat = litteral_to_latex;
    litt_format = "%s";
    dual_format = "{%s}\\orth";
    is_dual_atomic = true;
    is_unary_atomic = true;
    one_format = "\\one";
    bottom_format = "\\bot";
    top_format = "\\top";
    zero_format = "\\zero";
    tensor_format = "%s \\tensor %s";
    par_format = "%s \\parr %s";
    with_format = "%s \\with %s";
    plus_format = "%s \\plus %s";
    ofcourse_format = "\\oc %s";
    whynot_format = "\\wn %s" }

let formula_to_latex formula =
  let s, _ = formula_export_atomic latex_format formula in s

let sequent_to_latex sequent =
    String.concat ", " (List.map formula_to_latex sequent);;


(* SEQUENT -> ASCII *)

let ascii_format = {
    atom_preformat = (fun x -> x);
    litt_format = "%s";
    dual_format = "%s^";
    is_dual_atomic = true;
    is_unary_atomic = true;
    one_format = "1";
    bottom_format = "_";
    top_format = "T";
    zero_format = "0";
    tensor_format = "%s * %s";
    par_format = "%s | %s";
    with_format = "%s & %s";
    plus_format = "%s + %s";
    ofcourse_format = "!%s";
    whynot_format = "?%s" }

let formula_to_ascii formula =
  let s, _ = formula_export_atomic ascii_format formula in s

let sequent_to_ascii utf8 sequent =
  (if utf8 then "|-" else "|- ")
  ^ (String.concat ", " (List.map formula_to_ascii sequent));;
