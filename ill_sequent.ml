(* DEFINITION OF INTUITIONISTIC LINEAR LOGIC FORMULAS AND SEQUENTS *)

(* The core data structure representing Intuitionistic Linear Logic formulas.
   ILL is a resource-sensitive logic like LL, but with an asymmetric sequent calculus
   where formulas can only appear on the right side of the turnstile.
   
   Key differences from Linear Logic:
   - No multiplicative disjunction (⅋) - removed  
   - No whynot (?A) - removed
   - Has exponential modality (!A) for structural rules
   - Only has: 1, ⊗, ⊤, &, ⊕, ⊸, ! (of course)
   
   The formula constructors represent:
   - One: multiplicative unit (1)
   - Top: additive unit (⊤) 
   - Litt: atomic proposition (literal like A, B, C)
   - Tensor: multiplicative conjunction (A ⊗ B) - "both A and B"
   - With: additive conjunction (A & B) - "both A and B, but choose one to use"
   - Plus: additive disjunction (A ⊕ B) - "A or B, choose one"
   - Lollipop: linear implication (A ⊸ B) - "A implies B linearly"
   - Ofcourse: exponential modality (!A) - "unlimited copies of A"
*)
type formula =
  | One
  | Top
  | Litt of string
  | Tensor of formula * formula
  | With of formula * formula
  | Plus of formula * formula
  | Lollipop of formula * formula
  | Ofcourse of formula;;

(* A sequent in ILL is represented as Γ ⊢ A where:
   - Γ is a list of formulas (the context/assumptions)
   - A is a single formula (the goal)
   This is different from classical LL which allows multiple conclusions.
*)
type ill_sequent = {
  context: formula list;  (* Γ - the assumptions *)
  goal: formula;          (* A - the conclusion *)
};;

(* Convert a traditional sequent list to ILL sequent structure.
   In ILL, we expect exactly one formula on the right side.
   If there are multiple, we fail or combine them somehow.
*)
let sequent_list_to_ill_sequent = function
  | [] -> failwith "ILL sequent must have a goal"
  | [goal] -> { context = []; goal = goal }
  | goal :: context -> { context = List.rev context; goal = goal }

(* Convert ILL sequent back to list format for compatibility *)
let ill_sequent_to_list ill_seq =
  ill_seq.context @ [ill_seq.goal]

(* CORE OPERATIONS ON ILL FORMULAS *)

(* Convert a sequent (list of formulas) to a single formula.
   In ILL, we use tensor to combine multiple assumptions.
*)
let rec context_to_formula = function
  | [] -> One
  | [f] -> f
  | f1 :: f2 :: context -> context_to_formula (Tensor (f1, f2) :: context)

(* ILL doesn't have classical duality like LL, but we can define
   a limited form for atomic propositions if needed for compatibility.
*)
let dual_atom = function
  | Litt x -> Litt (x ^ "^")  (* Simple syntactic dual *)
  | _ -> failwith "ILL dual only defined for atoms"

(* Extract all variable names (literals) from an ILL formula *)
let rec get_variable_names =
    function
    | One -> []
    | Top -> []
    | Litt x -> [x]
    | Tensor (e1, e2) -> get_variable_names e1 @ get_variable_names e2
    | With (e1, e2) -> get_variable_names e1 @ get_variable_names e2
    | Plus (e1, e2) -> get_variable_names e1 @ get_variable_names e2
    | Lollipop (e1, e2) -> get_variable_names e1 @ get_variable_names e2
    | Ofcourse e -> get_variable_names e;;

(* Get all unique variable names from an ILL sequent *)
let get_unique_variable_names ill_seq =
    let all_formulas = ill_seq.context @ [ill_seq.goal] in
    List.sort_uniq String.compare (List.concat_map get_variable_names all_formulas);;

(* PATTERN MATCHING ON ILL FORMULAS *)

let is_top = function | Top -> true | _ -> false;;
let is_tensor = function | Tensor _ -> true | _ -> false;;
let is_with = function | With _ -> true | _ -> false;;
let is_plus = function | Plus _ -> true | _ -> false;;
let is_lollipop = function | Lollipop _ -> true | _ -> false;;
let is_ofcourse = function | Ofcourse _ -> true | _ -> false;;

(* EXPORT FORMATS FOR ILL *)

(* Export ILL formula to ASCII representation *)
let rec formula_to_ascii = function
  | One -> "1"
  | Top -> "T" 
  | Litt x -> x
  | Tensor (e1, e2) -> "(" ^ formula_to_ascii e1 ^ " * " ^ formula_to_ascii e2 ^ ")"
  | With (e1, e2) -> "(" ^ formula_to_ascii e1 ^ " & " ^ formula_to_ascii e2 ^ ")"
  | Plus (e1, e2) -> "(" ^ formula_to_ascii e1 ^ " + " ^ formula_to_ascii e2 ^ ")"
  | Lollipop (e1, e2) -> "(" ^ formula_to_ascii e1 ^ " -o " ^ formula_to_ascii e2 ^ ")"
  | Ofcourse e -> "!" ^ formula_to_ascii e

(* Export ILL sequent to ASCII representation *)
let ill_sequent_to_ascii ill_seq =
  let context_str = String.concat ", " (List.map formula_to_ascii ill_seq.context) in
  let goal_str = formula_to_ascii ill_seq.goal in
  if ill_seq.context = [] then
    "|- " ^ goal_str
  else
    context_str ^ " |- " ^ goal_str

(* Export ILL formula to LaTeX representation *)
let rec formula_to_latex = function
  | One -> "\\one"
  | Top -> "\\top"
  | Litt x -> x
  | Tensor (e1, e2) -> formula_to_latex e1 ^ " \\otimes " ^ formula_to_latex e2
  | With (e1, e2) -> formula_to_latex e1 ^ " \\& " ^ formula_to_latex e2
  | Plus (e1, e2) -> formula_to_latex e1 ^ " \\oplus " ^ formula_to_latex e2
  | Lollipop (e1, e2) -> formula_to_latex e1 ^ " \\multimap " ^ formula_to_latex e2
  | Ofcourse e -> "!" ^ formula_to_latex e

(* Export ILL sequent to LaTeX representation *)
let ill_sequent_to_latex ill_seq =
  let context_str = String.concat ", " (List.map formula_to_latex ill_seq.context) in
  let goal_str = formula_to_latex ill_seq.goal in
  if ill_seq.context = [] then
    "\\vdash " ^ goal_str
  else
    context_str ^ " \\vdash " ^ goal_str