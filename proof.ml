open Sequent
open Rule_request

(* PROOF TREE REPRESENTATION
   
   This module defines the core data structure for Linear Logic proofs
   and operations for constructing and manipulating proof trees.
   
   Each proof is represented as a tree where:
   - Leaves are axioms or hypotheses
   - Internal nodes are inference rules with their premises as children
   - The root represents the conclusion sequent
*)

(* Algebraic data type representing Linear Logic proof trees.
   Each constructor corresponds to an inference rule in the sequent calculus.
   
   The naming pattern is: [Rule]_proof with the rule's conclusion data and premises.
   For example, Tensor_proof stores the tensor formula being decomposed,
   its context, and the two sub-proofs for the left and right components.
*)
type proof =
    | Axiom_proof of formula                                                      (* ax: A, A^ *)
    | One_proof                                                                   (* 1: ⊢ 1 *)  
    | Top_proof of formula list * formula list                                   (* ⊤: Γ, ⊤, Δ *)
    | Bottom_proof of formula list * formula list * proof                        (* ⊥: Γ, ⊥, Δ / Γ, Δ *)
    | Tensor_proof of formula list * formula * formula * formula list * proof * proof  (* ⊗: Γ, A⊗B, Δ / Γ₁, A / B, Δ₁ *)
    | Par_proof of formula list * formula * formula * formula list * proof       (* ⅋: Γ, A⅋B, Δ / Γ, A, B, Δ *)
    | With_proof of formula list * formula * formula * formula list * proof * proof   (* &: Γ, A&B, Δ / Γ, A, Δ & Γ, B, Δ *)
    | Plus_left_proof of formula list * formula * formula * formula list * proof      (* ⊕₁: Γ, A⊕B, Δ / Γ, A, Δ *)
    | Plus_right_proof of formula list * formula * formula * formula list * proof     (* ⊕₂: Γ, A⊕B, Δ / Γ, B, Δ *)
    | Promotion_proof of formula list * formula * formula list * proof           (* !: ?Γ, !A, ?Δ / ?Γ, A, ?Δ *)
    | Dereliction_proof of formula list * formula * formula list * proof         (* ?d: Γ, ?A, Δ / Γ, A, Δ *)
    | Weakening_proof of formula list * formula * formula list * proof           (* ?w: Γ, ?A, Δ / Γ, Δ *)
    | Contraction_proof of formula list * formula * formula list * proof         (* ?c: Γ, ?A, Δ / Γ, ?A, ?A, Δ *)
    | Exchange_proof of sequent * int list * int list * proof                    (* ech: permute formulas *)
    | Cut_proof of formula list * formula * formula list * proof * proof         (* cut: Γ, Δ / Γ, A & A^, Δ *)
    | Unfold_litt_proof of formula list * string * formula list * proof          (* def: unfold notation *)
    | Unfold_dual_proof of formula list * string * formula list * proof          (* def: unfold dual notation *)
    | Hypothesis_proof of sequent;;                                              (* open goal (leaf) *)


(* PERMUTATIONS *)

let identity n = List.init n (fun k -> k)

let is_valid_permutation l =
    let sorted_l = List.sort Int.compare l in
    sorted_l = identity (List.length l);;

let permute l =
    List.map (List.nth l);;

let rec position_in_list a = function
    | [] -> raise (Failure "Not found")
    | h :: tl -> if a = h then 0 else 1 + position_in_list a tl

let permutation_inverse perm =
    List.map (fun x -> position_in_list x perm) (identity (List.length perm))


(* GETTERS & SETTERS *)

let get_premises = function
    | Axiom_proof _ -> []
    | One_proof -> []
    | Top_proof (_, _) -> []
    | Bottom_proof (_, _, p) -> [p]
    | Tensor_proof (_, _, _, _, p1, p2) -> [p1; p2]
    | Par_proof (_, _, _, _, p) -> [p]
    | With_proof (_, _, _, _, p1, p2) -> [p1; p2]
    | Plus_left_proof (_, _, _, _, p) -> [p]
    | Plus_right_proof (_, _, _, _, p) -> [p]
    | Promotion_proof (_, _, _, p) -> [p]
    | Dereliction_proof (_, _, _, p) -> [p]
    | Weakening_proof (_, _, _, p) -> [p]
    | Contraction_proof (_, _, _, p) -> [p]
    | Exchange_proof (_, _, _, p) -> [p]
    | Cut_proof (_, _, _, p1, p2) -> [p1; p2]
    | Unfold_litt_proof (_, _, _, p) -> [p]
    | Unfold_dual_proof (_, _, _, p) -> [p]
    | Hypothesis_proof _ -> [];;

let set_premises proof premises = match proof, premises with
    | Axiom_proof _, [] -> proof
    | One_proof, [] -> proof
    | Top_proof (_, _), [] -> proof
    | Bottom_proof (head, tail, _), [p] -> Bottom_proof (head, tail, p)
    | Tensor_proof (head, e1, e2, tail, _, _), [p1; p2] -> Tensor_proof (head, e1, e2, tail, p1, p2)
    | Par_proof (head, e1, e2, tail, _), [p]  -> Par_proof (head, e1, e2, tail, p)
    | With_proof (head, e1, e2, tail, _, _), [p1; p2] -> With_proof (head, e1, e2, tail, p1, p2)
    | Plus_left_proof (head, e1, e2, tail, _), [p] -> Plus_left_proof (head, e1, e2, tail, p)
    | Plus_right_proof (head, e1, e2, tail, _), [p] -> Plus_right_proof (head, e1, e2, tail, p)
    | Promotion_proof (head_without_whynot, e, tail_without_whynot, _), [p] ->
        Promotion_proof (head_without_whynot, e, tail_without_whynot, p)
    | Dereliction_proof (head, e, tail, _), [p] -> Dereliction_proof (head, e, tail, p)
    | Weakening_proof (head, e, tail, _), [p] -> Weakening_proof (head, e, tail, p)
    | Contraction_proof (head, e, tail, _), [p] -> Contraction_proof (head, e, tail, p)
    | Exchange_proof (sequent, display_permutation, permutation, _), [p] -> Exchange_proof (sequent, display_permutation, permutation, p)
    | Cut_proof (head, e, tail, _, _), [p1; p2] -> Cut_proof (head, e, tail, p1, p2)
    | Unfold_litt_proof (head, s, tail, _), [p] -> Unfold_litt_proof (head, s, tail, p)
    | Unfold_dual_proof (head, s, tail, _), [p] -> Unfold_dual_proof (head, s, tail, p)
    | Hypothesis_proof _, [] -> proof
    | _ -> raise (Failure "Number of premises mismatch with given proof");;

let get_conclusion = function
    | Axiom_proof e -> [e; dual e]
    | One_proof -> [Sequent.One]
    | Top_proof (head, tail) -> head @ [Sequent.Top] @ tail
    | Bottom_proof (head, tail, _) -> head @ [Sequent.Bottom] @ tail
    | Tensor_proof (head, e1, e2, tail, _, _) -> head @ [Sequent.Tensor (e1, e2)] @ tail
    | Par_proof (head, e1, e2, tail, _) -> head @ [Sequent.Par (e1, e2)] @ tail
    | With_proof (head, e1, e2, tail, _, _) -> head @ [Sequent.With (e1, e2)] @ tail
    | Plus_left_proof (head, e1, e2, tail, _) -> head @ [Plus (e1, e2)] @ tail
    | Plus_right_proof (head, e1, e2, tail, _) -> head @ [Plus (e1, e2)] @ tail
    | Promotion_proof (head_without_whynot, e, tail_without_whynot, _) ->
        let head = Sequent.add_whynot head_without_whynot in
        let tail = Sequent.add_whynot tail_without_whynot in
        head @ [Ofcourse e] @ tail
    | Dereliction_proof (head, e, tail, _) -> head @ [Whynot e] @ tail
    | Weakening_proof (head, e, tail, _) -> head @ [Whynot e] @ tail
    | Contraction_proof (head, e, tail, _) -> head @ [Whynot e] @ tail
    | Exchange_proof (sequent, _, permutation, _) -> permute sequent permutation
    | Cut_proof (head, _, tail, _, _) -> head @ tail
    | Unfold_litt_proof (head, s, tail, _) -> head @ [Litt s] @ tail
    | Unfold_dual_proof (head, s, tail, _) -> head @ [Dual s] @ tail
    | Hypothesis_proof sequent -> sequent;;


(* REPLACEMENTS *)

let rec replace_in_proof a f = function
    | Axiom_proof e ->
        Axiom_proof (replace_in_formula a f e)
    | One_proof ->
        One_proof
    | Top_proof (head, tail) ->
        Top_proof (replace_in_sequent a f head, replace_in_sequent a f tail)
    | Bottom_proof (head, tail, p) ->
        Bottom_proof (replace_in_sequent a f head, replace_in_sequent a f tail, replace_in_proof a f p)
    | Tensor_proof (head, e1, e2, tail, p1, p2) ->
        Tensor_proof (replace_in_sequent a f head, replace_in_formula a f e1, replace_in_formula a f e2, replace_in_sequent a f tail, replace_in_proof a f p1, replace_in_proof a f p2)
    | Par_proof (head, e1, e2, tail, p)  ->
        Par_proof (replace_in_sequent a f head, replace_in_formula a f e1, replace_in_formula a f e2, replace_in_sequent a f tail, replace_in_proof a f p)
    | With_proof (head, e1, e2, tail, p1, p2) ->
        With_proof (replace_in_sequent a f head, replace_in_formula a f e1, replace_in_formula a f e2, replace_in_sequent a f tail, replace_in_proof a f p1, replace_in_proof a f p2)
    | Plus_left_proof (head, e1, e2, tail, p) ->
        Plus_left_proof (replace_in_sequent a f head, replace_in_formula a f e1, replace_in_formula a f e2, replace_in_sequent a f tail, replace_in_proof a f p)
    | Plus_right_proof (head, e1, e2, tail, p) ->
        Plus_right_proof (replace_in_sequent a f head, replace_in_formula a f e1, replace_in_formula a f e2, replace_in_sequent a f tail, replace_in_proof a f p)
    | Promotion_proof (head_without_whynot, e, tail_without_whynot, p) ->
        Promotion_proof (replace_in_sequent a f head_without_whynot, replace_in_formula a f e, replace_in_sequent a f tail_without_whynot, replace_in_proof a f p)
    | Dereliction_proof (head, e, tail, p) ->
        Dereliction_proof (replace_in_sequent a f head, replace_in_formula a f e, replace_in_sequent a f tail, replace_in_proof a f p)
    | Weakening_proof (head, e, tail, p) ->
        Weakening_proof (replace_in_sequent a f head, replace_in_formula a f e, replace_in_sequent a f tail, replace_in_proof a f p)
    | Contraction_proof (head, e, tail, p) ->
        Contraction_proof (replace_in_sequent a f head, replace_in_formula a f e, replace_in_sequent a f tail, replace_in_proof a f p)
    | Exchange_proof (sequent, display_permutation, permutation, p) ->
        Exchange_proof (replace_in_sequent a f sequent, display_permutation, permutation, replace_in_proof a f p)
    | Cut_proof (head, e, tail, p1, p2) ->
        Cut_proof (replace_in_sequent a f head, replace_in_formula a f e, replace_in_sequent a f tail, replace_in_proof a f p1, replace_in_proof a f p2)
    | Unfold_litt_proof (head, s, tail, p) ->
        if s = a then raise (Failure "Can not substitute an atom that is notation name") else
        Unfold_litt_proof (replace_in_sequent a f head, s, replace_in_sequent a f tail, replace_in_proof a f p)
    | Unfold_dual_proof (head, s, tail, p) ->
        if s = a then raise (Failure "Can not substitute an atom that is notation name") else
        Unfold_dual_proof (replace_in_sequent a f head, s, replace_in_sequent a f tail, replace_in_proof a f p)
    | Hypothesis_proof s ->
        Hypothesis_proof (replace_in_sequent a f s);;

(* VARIABLES *)

let rec get_variable_names proof =
    let variables = Sequent.get_unique_variable_names (get_conclusion proof) in
    variables @ List.concat_map get_variable_names (get_premises proof);;

let get_unique_variable_names proof =
    List.sort_uniq String.compare (get_variable_names proof);;


(* SEQUENT & RULE_REQUEST -> PROOF *)

exception Rule_exception of bool * string;;

let rec head_formula_tail n = function
    | [] -> raise (Rule_exception (false, "Argument formula_position is greater than the sequent"))
    | f :: formula_list -> if n = 0 then [], f, formula_list
        else let head, formula, tail = head_formula_tail (n - 1) formula_list
        in f::head, formula, tail;;

let rec slice l n =
    if n = 0 then [], l else
    match l with
    | [] -> raise (Rule_exception (false, "Argument formula_position is greater than the sequent"))
    | e :: l' -> let head, tail = slice l' (n - 1) in e::head, tail;;

let from_sequent_and_rule_request sequent notations = function
    | Axiom -> (
        match sequent with
        | [e1; e2] -> (if dual e1 <> e2
            then raise (Rule_exception (true, "Can not apply 'axiom' rule: the two formulas are not orthogonal.")));
            Axiom_proof e1
        | _ -> raise (Rule_exception (true, "Can not apply 'axiom' rule: the sequent must contain exactly two formulas."))
    )
    | One -> (
        match sequent with
        | [One] -> One_proof
        | _ -> raise (Rule_exception (true, "Can not apply 'one' rule: the sequent must be reduced to the single formula '1'."))
    )
    | Bottom n -> (
        let head, formula, tail = head_formula_tail n sequent in
        match formula with
        | Bottom -> Bottom_proof (head, tail, (Hypothesis_proof (head @ tail)))
        | _ -> raise (Rule_exception (false, "Cannot apply bottom rule on this formula"))
    )
    | Top n -> (
        let head, formula, tail = head_formula_tail n sequent in
        match formula with
        | Top -> Top_proof (head, tail)
        | _ -> raise (Rule_exception (false, "Cannot apply top rule on this formula"))
    )
    | Zero -> raise (Rule_exception (true, "Can not apply 'zero' rule: there is no rule for introducing '0'."))
    | Tensor n -> (
        let head, formula, tail = head_formula_tail n sequent in
        match formula with
        Tensor (e1, e2) -> Tensor_proof (head, e1, e2, tail, (Hypothesis_proof (head @ [e1])), (Hypothesis_proof ([e2] @ tail)))
        | _ -> raise (Rule_exception (false, "Cannot apply tensor rule on this formula"))
    )
    | Par n -> (
        let head, formula, tail = head_formula_tail n sequent in
        match formula with
        Par (e1, e2) -> Par_proof (head, e1, e2, tail, (Hypothesis_proof (head @ [e1; e2] @ tail)))
        | _ -> raise (Rule_exception (false, "Cannot apply par rule on this formula"))
    )
    | With n -> (
        let head, formula, tail = head_formula_tail n sequent in
        match formula with
        With (e1, e2) -> With_proof (head, e1, e2, tail, (Hypothesis_proof (head @ [e1] @ tail)), (Hypothesis_proof (head @ [e2] @ tail)))
        | _ -> raise (Rule_exception (false, "Cannot apply with rule on this formula"))
    )
    | Plus_left n -> (
        let head, formula, tail = head_formula_tail n sequent in
        match formula with
        Plus (e1, e2) -> Plus_left_proof (head, e1, e2, tail, (Hypothesis_proof (head @ [e1] @ tail)))
        | _ -> raise (Rule_exception (false, "Cannot apply plus_left rule on this formula"))
    )
    | Plus_right n -> (
        let head, formula, tail = head_formula_tail n sequent in
        match formula with
        Plus (e1, e2) -> Plus_right_proof (head, e1, e2, tail, (Hypothesis_proof (head @ [e2] @ tail)))
        | _ -> raise (Rule_exception (false, "Cannot apply plus_right rule on this formula"))
    )
    | Promotion n -> (
        let head, formula, tail = head_formula_tail n sequent in
        match formula with
        Ofcourse e -> (try
            let head_without_whynot = Sequent.remove_whynot head in
            let tail_without_whynot = remove_whynot tail in
            Promotion_proof (head_without_whynot, e, tail_without_whynot, (Hypothesis_proof (head @ [e] @ tail)))
            with Sequent.Not_whynot -> raise (Rule_exception (true, "Can not apply 'promotion' rule: the context must contain formulas starting by '?' only.")))
        | _ -> raise (Rule_exception (false, "Cannot apply promotion rule on this formula"))
    )
    | Dereliction n -> (
        let head, formula, tail = head_formula_tail n sequent in
        match formula with
        Whynot e -> Dereliction_proof (head, e, tail, (Hypothesis_proof (head @ [e] @ tail)))
        | _ -> raise (Rule_exception (false, "Cannot apply dereliction rule on this formula"))
    )
    | Weakening n -> (
        let head, formula, tail = head_formula_tail n sequent in
        match formula with
        Whynot e -> Weakening_proof (head, e, tail, (Hypothesis_proof (head @ tail)))
        | _ -> raise (Rule_exception (false, "Cannot apply weakening rule on this formula"))
    )
    | Contraction n -> (
        let head, formula, tail = head_formula_tail n sequent in
        match formula with
        Whynot e -> Contraction_proof (head, e, tail, (Hypothesis_proof (head @ [Whynot e; Whynot e] @ tail)))
        | _ -> raise (Rule_exception (false, "Cannot apply contraction rule on this formula"))
    )
    | Exchange (display_permutation, permutation) -> (
        if List.length sequent <> List.length permutation
        then raise (Rule_exception (false, "When applying exchange rule, formula_positions and sequent must have same size"))
        else if not (is_valid_permutation permutation)
        then raise (Rule_exception (false, "When applying exchange rule, formula_positions should be a permutation of the size of sequent formula list"))
        else let permuted_sequent = permute sequent (permutation_inverse permutation) in
             Exchange_proof (permuted_sequent, display_permutation, permutation, Hypothesis_proof permuted_sequent)
    )
    | Cut (formula, n) -> (
        let head, tail = slice sequent n in
        Cut_proof (head, formula, tail, Hypothesis_proof (head @ [formula]), Hypothesis_proof ([dual formula] @ tail))
    )
    | Unfold_litt n -> (
        let head, formula, tail = head_formula_tail n sequent in
        match formula with
        | Litt s -> begin
            try let definition = Raw_sequent.to_formula (List.assoc s notations) in
            Unfold_litt_proof (head, s, tail, Hypothesis_proof (head @ [definition] @ tail))
            with Not_found -> raise (Rule_exception (false, "Cannot apply unfold_litt rule on this litt as it does not belong to definition")) end
        | _ -> raise (Rule_exception (false, "Cannot apply unfold_litt rule on this formula"))
    )
    | Unfold_dual n -> (
        let head, formula, tail = head_formula_tail n sequent in
        match formula with
        | Dual s -> begin
            try let definition = Raw_sequent.to_formula (List.assoc s notations) in
            Unfold_dual_proof (head, s, tail, Hypothesis_proof (head @ [dual definition] @ tail))
            with Not_found -> raise (Rule_exception (false, "Cannot apply unfold_dual rule on this litt as it does not belong to definition")) end
        | _ -> raise (Rule_exception (false, "Cannot apply unfold_dual rule on this formula"))
    );;

let from_sequent_and_rule_request_and_premises sequent notations rule_request premises =
    let proof = from_sequent_and_rule_request sequent notations rule_request in
    let expected_premises_conclusion = List.map get_conclusion (get_premises proof) in
    let given_premises_conclusion = List.map get_conclusion premises in
    if expected_premises_conclusion <> given_premises_conclusion then
    raise (Rule_exception (false, Printf.sprintf "Premises conclusion do not match expected premises conclusion after applying rule %s}" (Rule_request.to_string rule_request)))
    else set_premises proof premises;;

(* AUTO REVERSE MODE *)

exception NotApplicable;;

let rec get_formula_position condition = function
    | [] -> raise NotApplicable
    | f :: tail -> if condition f then 0 else 1 + (get_formula_position condition tail);;

let try_rule_request sequent rule_request =
    (* Auto-reverse ignores notations *)
    try from_sequent_and_rule_request sequent [] rule_request
    with Rule_exception _ -> raise NotApplicable;;

let starts_with_notation notations = function
    | Litt s :: _ -> List.mem_assoc s notations
    | Dual s :: _ -> List.mem_assoc s notations
    | _ -> false;;

let apply_reversible_rule notations proof =
    let sequent = get_conclusion proof in
    try try_rule_request sequent (Top (get_formula_position is_top sequent))
        with NotApplicable ->
    try try_rule_request sequent (Bottom (get_formula_position is_bottom sequent))
        with NotApplicable ->
    try try_rule_request sequent (Par (get_formula_position is_par sequent))
        with NotApplicable ->
    try try_rule_request sequent (With (get_formula_position is_with sequent))
        with NotApplicable ->
    try try_rule_request sequent (Promotion (get_formula_position is_ofcourse sequent))
        with NotApplicable ->
    try try_rule_request sequent One
        with NotApplicable ->
    try if List.length sequent = 1 then try_rule_request sequent (Tensor 0) else raise NotApplicable
        with NotApplicable ->
    try if not (starts_with_notation notations sequent) then try_rule_request sequent Axiom else raise NotApplicable
        with NotApplicable ->
    proof;;

let rec rec_apply_reversible_rule notations proof =
    let new_proof = apply_reversible_rule notations proof in
    let premises = get_premises new_proof in
    let new_premises = List.map (rec_apply_reversible_rule notations) premises in
    set_premises new_proof new_premises;;

(* AUTO WEAK MODE *)
exception AutoWeakNotApplicable;;

let rec auto_weak = function
    | [] -> raise AutoWeakNotApplicable
    | [Sequent.One] -> One_proof
    | [_e] -> raise AutoWeakNotApplicable
    | [e1; e2] when e1 = dual e2 -> Axiom_proof e1
    | [One; Whynot f] -> Weakening_proof ([One], f, [], One_proof)
    | [Whynot f; One] -> Weakening_proof ([], f, [One], One_proof)
    | [_e1; _e2] -> raise AutoWeakNotApplicable
    | Whynot f :: tail when not (List.mem (dual (Whynot f)) tail) ->
        Weakening_proof ([], f, tail, auto_weak tail)
    | e :: Whynot f :: tail when e <> dual (Whynot f) ->
       Weakening_proof ([e], f, tail, auto_weak (e :: tail))
    | e1 :: e2 :: Whynot f :: tail ->
       Weakening_proof ([e1; e2], f, tail, auto_weak (e1 :: e2 :: tail))
    | _ -> raise AutoWeakNotApplicable;;

(* PROOF -> RULE REQUEST *)

let get_rule_request = function
    | Axiom_proof _ -> Axiom
    | One_proof -> One
    | Top_proof (head, _) -> Top (List.length head)
    | Bottom_proof (head, _, _) -> Bottom (List.length head)
    | Tensor_proof (head, _, _, _, _, _) -> Tensor (List.length head)
    | Par_proof (head, _, _, _, _) -> Par (List.length head)
    | With_proof (head, _, _, _, _, _) -> With (List.length head)
    | Plus_left_proof (head, _, _, _, _) -> Plus_left (List.length head)
    | Plus_right_proof (head, _, _, _, _) -> Plus_right (List.length head)
    | Promotion_proof (head_without_whynot, _, _, _) -> Promotion (List.length head_without_whynot)
    | Dereliction_proof (head, _, _, _) -> Dereliction (List.length head)
    | Weakening_proof (head, _, _, _) -> Weakening (List.length head)
    | Contraction_proof (head, _, _, _) -> Contraction (List.length head)
    | Exchange_proof (_, display_permutation, permutation, _) -> Exchange (display_permutation, permutation)
    | Cut_proof (head, formula, _, _, _) -> Cut (formula, List.length head)
    | Unfold_litt_proof (head, _, _, _) -> Unfold_litt (List.length head)
    | Unfold_dual_proof (head, _, _, _) -> Unfold_dual (List.length head)
    | Hypothesis_proof _ -> raise (Failure "Can not get rule request of hypothesis");;


(* JSON -> PROOF *)

exception Json_exception of string;;

let optional_field json key =
    let value =
        try Yojson.Basic.Util.member key json
        with Yojson.Basic.Util.Type_error (_, _) -> raise (Json_exception ("a proof must be a json object"))
    in
    value;;

let required_field json key =
    let value = optional_field json key in
    if value = `Null
    then raise (Json_exception ("required field '" ^ key ^ "' is missing"))
    else value;;

let get_json_list json key =
    let value = required_field json key in
    try Yojson.Basic.Util.to_list value
    with Yojson.Basic.Util.Type_error (_, _) -> raise (Json_exception ("field '" ^ key ^ "' must be a list"));;

let rec from_json notations json =
    let sequent_as_json = required_field json "sequent" in
    let sequent = Raw_sequent.sequent_from_json sequent_as_json in
    let applied_ruled_as_json = optional_field json "appliedRule" in
    match applied_ruled_as_json with
        | `Null -> Hypothesis_proof sequent
        | _ -> let rule_request_as_json = required_field applied_ruled_as_json "ruleRequest" in
            let rule_request = Rule_request.from_json rule_request_as_json in
            let premises_as_json = get_json_list applied_ruled_as_json "premises" in
            let premises = List.map (from_json notations) premises_as_json in
            from_sequent_and_rule_request_and_premises sequent notations rule_request premises;;


(* PROOF -> JSON *)

let rec to_json ?add_options:(add_options=fun _proof -> []) proof =
    let sequent = get_conclusion proof in
    let sequent_as_json = Raw_sequent.sequent_to_json sequent in
    match proof with
    | Hypothesis_proof _ -> `Assoc [("sequent", sequent_as_json);
                                    ("appliedRule", `Null)]
    | _ ->
        let rule_request = get_rule_request proof in
        let rule_request_as_json = Rule_request.to_json rule_request in
        let premises = get_premises proof in
        let premises_as_json = List.map (to_json ~add_options:add_options) premises in
        let applied_rule = [("ruleRequest", rule_request_as_json); ("premises", `List premises_as_json)] @ (add_options proof) in
        `Assoc [("sequent", sequent_as_json);
                ("appliedRule", `Assoc applied_rule)];;


(* PROOF -> COQ *)

let coq_apply coq_rule =
    Printf.sprintf "apply %s; cbn_sequent.\n" coq_rule;;

let coq_apply_with_args coq_rule args =
    let args_as_string = (String.concat " " args) in
    Printf.sprintf "apply (%s %s); cbn_sequent.\n" coq_rule args_as_string;;

let coq_unfold_at_position cyclic_notations notation_name head =
    let position = Sequent.count_notation notation_name head + 1 in
    let unfold_command =
      if List.mem_assoc notation_name cyclic_notations
      then Printf.sprintf "pattern %s at %d; rewrite Hyp_%s" notation_name position notation_name
      else Printf.sprintf "unfold %s at %d" notation_name position in
    Printf.sprintf "%s; cbn_sequent.\n" unfold_command;;

let permutation_to_coq permutation =
    Printf.sprintf "[%s]" (String.concat "; " (List.map string_of_int permutation));;

let indent_line line =
    "  " ^ line;;

let add_indent_and_brace proof_as_coq =
    let lines = List.filter (fun s -> s <> "") (String.split_on_char '\n' proof_as_coq) in
    let indented_lines =
      match lines with
      | [] -> raise (Failure "Empty generated Coq proof")
      | first_line :: other_lines -> first_line :: List.map indent_line other_lines
    in Printf.sprintf "{ %s }\n" (String.concat "\n" indented_lines)

let rec to_coq_with_hyps_increment cyclic_notations i = function
    | Axiom_proof _ -> "ax_expansion.\n", i, []
    | One_proof -> coq_apply "one_r_ext", i, []
    | Top_proof (head, _) -> coq_apply_with_args "top_r_ext" [formula_list_to_coq head], i, []
    | Bottom_proof (head, _, p) ->
        let s, n, hyps = to_coq_with_hyps_increment cyclic_notations i p in
        coq_apply_with_args "bot_r_ext" [formula_list_to_coq head] ^ s, n, hyps
    | Tensor_proof (head, _, _, _, p1, p2) ->
        let s1, n1, hyps1 = to_coq_with_hyps_increment cyclic_notations i p1 in
        let s2, n2, hyps2 = to_coq_with_hyps_increment cyclic_notations n1 p2 in
        coq_apply_with_args "tens_r_ext" [formula_list_to_coq head] ^ add_indent_and_brace s1 ^ add_indent_and_brace s2, n2, hyps1 @ hyps2
    | Par_proof (head, _, _, _, p) ->
        let s, n, hyps = to_coq_with_hyps_increment cyclic_notations i p in
        coq_apply_with_args "parr_r_ext" [formula_list_to_coq head] ^ s, n, hyps
    | With_proof (head, _, _, _, p1, p2) ->
        let s1, n1, hyps1 = to_coq_with_hyps_increment cyclic_notations i p1 in
        let s2, n2, hyps2 = to_coq_with_hyps_increment cyclic_notations n1 p2 in
        coq_apply_with_args "with_r_ext" [formula_list_to_coq head] ^ add_indent_and_brace s1 ^ add_indent_and_brace s2, n2, hyps1 @ hyps2
    | Plus_left_proof (head, _, _, _, p) ->
        let s, n, hyps = to_coq_with_hyps_increment cyclic_notations i p in
        coq_apply_with_args "plus_r1_ext" [formula_list_to_coq head] ^ s, n, hyps
    | Plus_right_proof (head, _, _, _, p) ->
        let s, n, hyps = to_coq_with_hyps_increment cyclic_notations i p in
        coq_apply_with_args "plus_r2_ext" [formula_list_to_coq head] ^ s, n, hyps
    | Promotion_proof (head_without_whynot, e, tail_without_whynot, p) ->
        let s, n, hyps = to_coq_with_hyps_increment cyclic_notations i p in
        coq_apply_with_args "oc_r_ext" [formula_list_to_coq head_without_whynot; "(" ^ formula_to_coq e ^ ")"; formula_list_to_coq tail_without_whynot] ^ s, n, hyps
    | Dereliction_proof (head, _, _, p) ->
        let s, n, hyps = to_coq_with_hyps_increment cyclic_notations i p in
        coq_apply_with_args "de_r_ext" [formula_list_to_coq head] ^ s, n, hyps
    | Weakening_proof (head, _, _, p) ->
        let s, n, hyps = to_coq_with_hyps_increment cyclic_notations i p in
        coq_apply_with_args "wk_r_ext" [formula_list_to_coq head] ^ s, n, hyps
    | Contraction_proof (head, _, _, p) ->
        let s, n, hyps = to_coq_with_hyps_increment cyclic_notations i p in
        coq_apply_with_args "co_r_ext" [formula_list_to_coq head] ^ s, n, hyps
    | Exchange_proof (sequent, _, permutation, p) ->
        let s, n, hyps = to_coq_with_hyps_increment cyclic_notations i p in
        coq_apply_with_args "ex_perm_r" [permutation_to_coq permutation; formula_list_to_coq sequent] ^ s, n, hyps
    | Cut_proof (head, cut, _, p1, p2) ->
        let s1, n1, hyps1 = to_coq_with_hyps_increment cyclic_notations i p1 in
        let s2, n2, hyps2 = to_coq_with_hyps_increment cyclic_notations n1 p2 in
        coq_apply_with_args "cut_r_ext" [formula_list_to_coq head; "(" ^ formula_to_coq cut ^ ")"] ^ add_indent_and_brace s1 ^ add_indent_and_brace s2, n2, hyps1 @ hyps2
    | Unfold_litt_proof (head, notation_name, _, p) ->
        let s, n, hyps = to_coq_with_hyps_increment cyclic_notations i p in
        coq_unfold_at_position cyclic_notations notation_name head ^ s, n, hyps
    | Unfold_dual_proof (head, notation_name, _, p) ->
        let s, n, hyps = to_coq_with_hyps_increment cyclic_notations i p in
        coq_unfold_at_position cyclic_notations notation_name head ^ s, n, hyps
    | Hypothesis_proof sequent -> coq_apply ("Hyp" ^ string_of_int i), i + 1, [Sequent.sequent_to_coq sequent];;

let to_coq_with_hyps cyclic_notations = to_coq_with_hyps_increment cyclic_notations 0


(* PROOF -> LATEX *)

let permutation_to_latex permutation =
    Printf.sprintf "(%s)" (String.concat "\\; " (List.map (fun n -> string_of_int (n + 1)) permutation));;

let latex_apply latex_rule conclusion =
    Printf.sprintf "  \\%s{%s}\n" latex_rule conclusion

let rec to_latex_permute implicit_exchange permutation_opt proof =
    (* implicit_exchange is true when we don't display exchange rule.
       permutation_opt is [None] when conclusion is to display as is,
       [Some permutation] if we need to permute it before *)
    let to_latex_clear_exchange = to_latex_permute implicit_exchange None in
    let conclusion =
      let preconclusion = get_conclusion proof in
      match permutation_opt with
      | None -> sequent_to_latex preconclusion
      | Some permutation -> sequent_to_latex (permute preconclusion permutation) in
    match proof with
    | Axiom_proof _ -> latex_apply "axv" conclusion
    | One_proof -> latex_apply "onev" conclusion
    | Top_proof _ -> latex_apply "topv" conclusion
    | Bottom_proof (_, _, p) -> to_latex_clear_exchange p ^ (latex_apply "botv" conclusion)
    | Tensor_proof (_, _, _, _, p1, p2) -> to_latex_clear_exchange p1 ^ (to_latex_clear_exchange p2) ^ (latex_apply "tensorv" conclusion)
    | Par_proof (_, _, _, _, p) -> to_latex_clear_exchange p ^ (latex_apply "parrv" conclusion)
    | With_proof (_, _, _, _, p1, p2) -> to_latex_clear_exchange p1 ^ (to_latex_clear_exchange p2) ^ (latex_apply "withv" conclusion)
    | Plus_left_proof (_, _, _, _, p) -> to_latex_clear_exchange p ^ (latex_apply "pluslv" conclusion)
    | Plus_right_proof (_, _, _, _, p) -> to_latex_clear_exchange p ^ (latex_apply "plusrv" conclusion)
    | Promotion_proof (_, _, _, p) -> to_latex_clear_exchange p ^ (latex_apply "ocv" conclusion)
    | Dereliction_proof (_, _, _, p) -> to_latex_clear_exchange p ^ (latex_apply "dev" conclusion)
    | Weakening_proof (_, _, _, p) -> to_latex_clear_exchange p ^ (latex_apply "wkv" conclusion)
    | Contraction_proof (_, _, _, p) -> to_latex_clear_exchange p ^ (latex_apply "cov" conclusion)
    | Exchange_proof (_, display_permutation, permutation, p) ->
        if implicit_exchange
            then to_latex_permute implicit_exchange (Some display_permutation) p
            else to_latex_permute implicit_exchange None p ^
                if permutation = identity (List.length permutation) then ""
                else let ex_with_permutation = Printf.sprintf "exv{%s}" (permutation_to_latex permutation)
                     in latex_apply ex_with_permutation conclusion
    | Cut_proof (_, _, _, p1, p2) -> to_latex_clear_exchange p1 ^ (to_latex_clear_exchange p2) ^ (latex_apply "cutv" conclusion)
    | Unfold_litt_proof (_, _, _, p) -> to_latex_clear_exchange p ^ (latex_apply "defv" conclusion)
    | Unfold_dual_proof (_, _, _, p) -> to_latex_clear_exchange p ^ (latex_apply "defv" conclusion)
    | Hypothesis_proof _ -> latex_apply "hypv" conclusion;;

let to_latex implicit_exchange =
    to_latex_permute implicit_exchange None

(* PROOF -> ASCII / UTF8 *)

(* as first step, proofs are translated as lists of ascii strings (all of the same length)
   with left_shift and right_shift giving the lateral position of conclusion
   then everything is concatenated
   and ascii can be converted to utf8 *)

type proof_text_list = int * int * string list

let left_shift_proof_text n =
  List.map (fun x -> String.make n ' ' ^ x)

let right_shift_proof_text n =
  List.map (fun x -> x ^ String.make n ' ')

let proof_text_width = function
  | [] -> 0
  | line :: _ -> String.length line

let concat_proof_text gap (left_shift1, _, proof1) (_, right_shift2, proof2) =
  let width1 = proof_text_width proof1 in
  let width2 = proof_text_width proof2 in
  let length1 = List.length proof1 in
  let length2 = List.length proof2 in
  let proof1_extended, proof2_extended = 
    if length1 > length2 then
      (proof1, List.init (length1 - length2) (fun _ -> String.make width2 ' ') @ proof2)
    else (List.init (length2 - length1) (fun _ -> String.make width1 ' ') @ proof1, proof2) in
  (left_shift1, right_shift2, List.map2 (fun line1 line2 -> line1 ^ (String.make gap ' ') ^ line2) proof1_extended proof2_extended)

let ascii_apply_hyp conclusion = (0, 0, [ conclusion ])

let ascii_apply0 rule_symbol rule_name conclusion =
  let width = String.length conclusion in
  let rule_name_width = String.length rule_name in
  (0, 1 + rule_name_width,
   [ Printf.sprintf "%s %s" (String.make width rule_symbol) rule_name;
     Printf.sprintf "%s %s" conclusion (String.make rule_name_width ' ') ])

let ascii_apply1 premise_data rule_symbol rule_name conclusion =
  let left_shift, right_shift, premise_text = premise_data in
  let premise_length = proof_text_width premise_text - (left_shift + right_shift) in
  let conclusion_length = String.length conclusion in
  let rule_length = max premise_length conclusion_length in
  let rule_name_width = String.length rule_name in
  let make_rule_line left right =
    Printf.sprintf "%s%s %s%s" (String.make left ' ') (String.make rule_length rule_symbol) rule_name (String.make right ' ') in
  let make_conclusion_line left right =
    Printf.sprintf "%s%s%s" (String.make left ' ') conclusion (String.make right ' ') in
  if premise_length > conclusion_length then
    let gap = premise_length - conclusion_length in
    let left_centering = gap / 2 in
    let right_centering = gap - left_centering in
    let right_rule_shift = right_shift - (1 + rule_name_width) in
    let right_enlarge = if right_rule_shift < 0 then - right_rule_shift else 0 in
    let rule_line = make_rule_line left_shift (right_rule_shift + right_enlarge) in
    let left_conclusion_shift = left_shift + left_centering in
    let right_conclusion_shift = right_centering + right_shift + right_enlarge in
    let conclusion_line = make_conclusion_line left_conclusion_shift right_conclusion_shift in
    (left_conclusion_shift, right_conclusion_shift,
     right_shift_proof_text right_enlarge premise_text @ [ rule_line; conclusion_line ])
  else
    let gap = conclusion_length - premise_length in
    let left_centering = gap / 2 in
    let right_centering = gap - left_centering in
    let left_rule_shift = left_shift - left_centering in
    let left_enlarge = if left_rule_shift < 0 then - left_rule_shift else 0 in
    let right_rule_shift = right_shift - (right_centering + 1 + rule_name_width) in
    let right_enlarge = if right_rule_shift < 0 then - right_rule_shift else 0 in
    let rule_line = make_rule_line (left_rule_shift + left_enlarge) (right_rule_shift + right_enlarge) in
    let left_conclusion_shift = left_rule_shift + left_enlarge in
    let right_conclusion_shift = right_rule_shift + right_enlarge + 1 + rule_name_width in
    let conclusion_line = make_conclusion_line left_conclusion_shift right_conclusion_shift in
    (left_conclusion_shift, right_conclusion_shift,
     left_shift_proof_text left_enlarge (right_shift_proof_text right_enlarge premise_text) @ [ rule_line; conclusion_line ])

let vertical_gap_ascii = 3

let rec to_ascii_list utf8 implicit_exchange permutation_opt proof =
    (* implicit_exchange is true when we don't display exchange rule.
       permutation_opt is [None] when conclusion is to display as is,
       [Some permutation] if we need to permute it before *)
    let to_ascii_list_clear_exchange = to_ascii_list utf8 implicit_exchange None in
    let conclusion =
      let preconclusion = get_conclusion proof in
      match permutation_opt with
      | None -> sequent_to_ascii utf8 preconclusion
      | Some permutation -> sequent_to_ascii utf8 (permute preconclusion permutation) in
    match proof with
    | Axiom_proof _ -> ascii_apply0 '-' "ax" conclusion
    | One_proof -> ascii_apply0 '-' "1" conclusion
    | Top_proof _ -> ascii_apply0 '-' "T" conclusion
    | Bottom_proof (_, _, p) -> ascii_apply1 (to_ascii_list_clear_exchange p) '-' "_" conclusion
    | Tensor_proof (_, _, _, _, p1, p2) ->
       let premise_data = concat_proof_text vertical_gap_ascii (to_ascii_list_clear_exchange p1) (to_ascii_list_clear_exchange p2) in
       ascii_apply1 premise_data '-' "*" conclusion
    | Par_proof (_, _, _, _, p) -> ascii_apply1 (to_ascii_list_clear_exchange p) '-' "|" conclusion
    | With_proof (_, _, _, _, p1, p2) ->
       let premise_data = concat_proof_text vertical_gap_ascii (to_ascii_list_clear_exchange p1) (to_ascii_list_clear_exchange p2) in
       ascii_apply1 premise_data '-' "&" conclusion
    | Plus_left_proof (_, _, _, _, p) -> ascii_apply1 (to_ascii_list_clear_exchange p) '-' "+1" conclusion
    | Plus_right_proof (_, _, _, _, p) -> ascii_apply1 (to_ascii_list_clear_exchange p) '-' "+2" conclusion
    | Promotion_proof (_, _, _, p) -> ascii_apply1 (to_ascii_list_clear_exchange p) '-' "!" conclusion
    | Dereliction_proof (_, _, _, p) -> ascii_apply1 (to_ascii_list_clear_exchange p) '-' "?d" conclusion
    | Weakening_proof (_, _, _, p) -> ascii_apply1 (to_ascii_list_clear_exchange p) '-' "?w" conclusion
    | Contraction_proof (_, _, _, p) -> ascii_apply1 (to_ascii_list_clear_exchange p) '-' "?c" conclusion
    | Exchange_proof (_, display_permutation, permutation, p) ->
        if implicit_exchange
            then to_ascii_list utf8 implicit_exchange (Some display_permutation) p
            else let premise_data = to_ascii_list utf8 implicit_exchange None p in
                if permutation = identity (List.length permutation) then premise_data
                else ascii_apply1 premise_data '-' "ex" conclusion
    | Cut_proof (_, _, _, p1, p2) ->
       let premise_data = concat_proof_text vertical_gap_ascii (to_ascii_list_clear_exchange p1) (to_ascii_list_clear_exchange p2) in
       ascii_apply1 premise_data '-' "cut" conclusion
    | Unfold_litt_proof (_, _, _, p) -> ascii_apply1 (to_ascii_list_clear_exchange p) '~' "def" conclusion
    | Unfold_dual_proof (_, _, _, p) -> ascii_apply1 (to_ascii_list_clear_exchange p) '~' "def" conclusion
    | Hypothesis_proof _ -> ascii_apply_hyp conclusion;;

let to_ascii_utf8 utf8 implicit_exchange notations proof =
    let _, _, proof_text = to_ascii_list utf8 implicit_exchange None proof in
    let max_name_width = List.fold_left (fun n (x, _) -> max n (String.length x)) 0 notations in
    let lines_list = List.map
        (fun (x, f) -> x ^ (String.make (max_name_width - String.length x) ' ') ^ " ::= " ^ Raw_sequent.raw_formula_to_ascii utf8 f)
        notations in
    (String.concat "\n" proof_text) ^ "\n" ^
        (if notations = [] then "" else "\n\n" ^ (String.concat "\n" lines_list) ^ "\n")

let to_ascii =
    to_ascii_utf8 false

let to_utf8 implicit_exchange notations proof =
    Str.global_replace (Str.regexp "+") "⊕"
   (Str.global_replace (Str.regexp "*") "⊗"
   (Str.global_replace (Str.regexp "|") "⅋"
   (Str.global_replace (Str.regexp "T") "⊤"
   (Str.global_replace (Str.regexp "_") "⊥"
   (Str.global_replace (Str.regexp "~") "-"
   (Str.global_replace (Str.regexp "-") "─"
   (Str.global_replace (Str.regexp "-o") " ⊸"
   (Str.global_replace (Str.regexp "|-") "⊢ "
   (to_ascii_utf8 true implicit_exchange notations proof)))))))))


(* PROOF & NOTATIONS *)

let rec from_fully_replaced_proof cyclic_notations acyclic_notations sequent proof =
    let rule_request = get_rule_request proof in
    try let new_proof = from_sequent_and_rule_request sequent [] rule_request in
        let new_sequents = List.map get_conclusion (get_premises new_proof) in
        let new_premises = List.map2 (from_fully_replaced_proof cyclic_notations acyclic_notations) new_sequents (get_premises proof) in
        set_premises new_proof new_premises
    with Rule_exception _ -> match rule_request with
    | Axiom -> unfold_axiom cyclic_notations acyclic_notations sequent proof
    | One -> unfold_at_position cyclic_notations acyclic_notations sequent proof 0
    | Top fp | Bottom fp | Tensor fp | Par fp | With fp | Plus_left fp | Plus_right fp | Promotion fp | Dereliction fp
    | Weakening fp | Contraction fp | Cut (_, fp) -> unfold_at_position cyclic_notations acyclic_notations sequent proof fp
    | _ -> raise (Failure (Printf.sprintf "rule_request %s not expected" (Rule_request.to_string rule_request)))

and unfold_at_position cyclic_notations acyclic_notations sequent proof position =
    let notations = acyclic_notations @ cyclic_notations in
    let new_proof = try
        from_sequent_and_rule_request sequent notations (Unfold_litt position) with Rule_exception _ ->
        from_sequent_and_rule_request sequent notations (Unfold_dual position) in
    let new_sequent = get_conclusion (List.hd (get_premises new_proof)) in
    set_premises new_proof [from_fully_replaced_proof cyclic_notations acyclic_notations new_sequent proof]

and unfold_axiom cyclic_notations acyclic_notations sequent proof =
    let new_proof = try
        from_sequent_and_rule_request sequent acyclic_notations (Unfold_litt 0) with Rule_exception _ -> try
        from_sequent_and_rule_request sequent acyclic_notations (Unfold_litt 1) with Rule_exception _ -> try
        from_sequent_and_rule_request sequent acyclic_notations (Unfold_dual 0) with Rule_exception _ -> try
        from_sequent_and_rule_request sequent acyclic_notations (Unfold_dual 1) with Rule_exception _ -> try
        from_sequent_and_rule_request sequent cyclic_notations (Unfold_litt 0) with Rule_exception _ -> try
        from_sequent_and_rule_request sequent cyclic_notations (Unfold_litt 1) with Rule_exception _ -> try
        from_sequent_and_rule_request sequent cyclic_notations (Unfold_dual 0) with Rule_exception _ ->
        from_sequent_and_rule_request sequent cyclic_notations (Unfold_dual 1) in
    let new_sequent = get_conclusion (List.hd (get_premises new_proof)) in
    set_premises new_proof [from_fully_replaced_proof cyclic_notations acyclic_notations new_sequent proof]
