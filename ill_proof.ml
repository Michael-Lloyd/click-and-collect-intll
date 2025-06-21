(* INTUITIONISTIC LINEAR LOGIC PROOF TREE REPRESENTATION
   
   This module defines proof trees for Intuitionistic Linear Logic (ILL).
   ILL differs from classical Linear Logic in several key ways:
   
   1. Asymmetric sequents: Γ ⊢ A (single conclusion)
   2. Has exponential: !A connective for structural rules
   3. No multiplicative disjunction: No ⅋ connective  
   4. Has additive conjunction: & connective
   5. Has linear implication: A ⊸ B connective
   
   Each proof tree node represents an inference rule application with its premises.
*)

open Ill_sequent

(* ILL proof tree data structure.
   Each constructor corresponds to an ILL inference rule.
   
   Key differences from classical LL proofs:
   - No Par_proof (removed connective)
   - Has exponential proofs for structural rules (!w, !c, !d, !p)
   - Added Lollipop_proof for linear implication
   - All sequents have single conclusions
*)
type ill_proof =
    | ILL_Axiom_proof of string                                           (* ax: A ⊢ A *)
    | ILL_One_proof                                                       (* 1: ⊢ 1 *)
    | ILL_Top_proof of formula list                                       (* ⊤: Γ ⊢ ⊤ *)
    | ILL_Tensor_proof of formula list * formula * formula * ill_proof * ill_proof  (* ⊗: Γ,Δ ⊢ A⊗B / Γ ⊢ A & Δ ⊢ B *)
    | ILL_Tensor_left_proof of formula list * formula * formula * ill_proof         (* ⊗L: Γ,A⊗B,Δ ⊢ C / Γ,A,B,Δ ⊢ C *)
    | ILL_With_left_1_proof of formula list * formula * ill_proof          (* &L₁: Γ,A&B ⊢ C / Γ,A ⊢ C *)
    | ILL_With_left_2_proof of formula list * formula * ill_proof          (* &L₂: Γ,A&B ⊢ C / Γ,B ⊢ C *)
    | ILL_With_right_proof of formula list * formula * formula * ill_proof * ill_proof  (* &R: Γ ⊢ A&B / Γ ⊢ A & Γ ⊢ B *)
    | ILL_Plus_left_proof of formula list * formula * formula * ill_proof * ill_proof  (* +L: Γ,A⊕B,Δ ⊢ C / Γ,A,Δ ⊢ C & Γ,B,Δ ⊢ C *)
    | ILL_Plus_right_1_proof of formula list * formula * formula * ill_proof      (* ⊕₁: Γ ⊢ A⊕B / Γ ⊢ A *)
    | ILL_Plus_right_2_proof of formula list * formula * formula * ill_proof      (* ⊕₂: Γ ⊢ A⊕B / Γ ⊢ B *)
    | ILL_Lollipop_proof of formula list * formula * formula * ill_proof           (* ⊸: Γ ⊢ A⊸B / Γ,A ⊢ B *)
    | ILL_Lollipop_left_proof of formula list * formula * formula * ill_proof * ill_proof  (* ⊸L: Γ,A⊸B,Δ ⊢ C / Γ ⊢ A & Δ,B ⊢ C *)
    | ILL_Cut_proof of formula list * formula * formula list * ill_proof * ill_proof  (* cut: Γ,Δ ⊢ C / Γ ⊢ A & Δ,A ⊢ C *)
    | ILL_Weakening_proof of formula list * formula * formula * ill_proof           (* !w: Γ,!A ⊢ B / Γ ⊢ B *)
    | ILL_Contraction_proof of formula list * formula * formula * ill_proof         (* !c: Γ,!A ⊢ B / Γ,!A,!A ⊢ B *)
    | ILL_Dereliction_proof of formula list * formula * formula * ill_proof         (* !d: Γ,!A ⊢ B / Γ,A ⊢ B *)
    | ILL_Promotion_proof of formula list * formula * ill_proof                     (* !p: !Γ ⊢ !A / !Γ ⊢ A *)
    | ILL_Hypothesis_proof of ill_sequent;;                              (* open goal (leaf) *)

(* Exception for invalid proof operations *)
exception ILL_Proof_Exception of bool * string;;

(* PROOF TREE MANIPULATION FUNCTIONS *)

(* Extract the conclusion sequent from a proof tree.
   Every proof tree proves some sequent - this extracts it.
   @param proof - ILL proof tree
   @return ill_sequent - The sequent that this proof establishes
*)
let rec get_conclusion_sequent = function
    | ILL_Axiom_proof atom -> 
        { context = [Litt atom]; goal = Litt atom }
    | ILL_One_proof -> 
        { context = []; goal = One }
    | ILL_Top_proof context -> 
        { context = context; goal = Top }
    | ILL_Tensor_proof (context, f1, f2, _, _) -> 
        { context = context; goal = Tensor (f1, f2) }
    | ILL_Tensor_left_proof (context, _, _, premise_proof) -> 
        { context = context; goal = (get_conclusion_sequent premise_proof).goal }
    | ILL_With_left_1_proof (context, _, premise_proof) -> 
        { context = context; goal = (get_conclusion_sequent premise_proof).goal }
    | ILL_With_left_2_proof (context, _, premise_proof) -> 
        { context = context; goal = (get_conclusion_sequent premise_proof).goal }
    | ILL_With_right_proof (context, f1, f2, _, _) -> 
        { context = context; goal = With (f1, f2) }
    | ILL_Plus_left_proof (context, _, _, premise1, _) -> 
        (* Both premises prove the same goal C, so we can use either one *)
        { context = context; goal = (get_conclusion_sequent premise1).goal }
    | ILL_Plus_right_1_proof (context, f1, f2, _) -> 
        { context = context; goal = Plus (f1, f2) }
    | ILL_Plus_right_2_proof (context, f1, f2, _) -> 
        { context = context; goal = Plus (f1, f2) }
    | ILL_Lollipop_proof (context, f1, f2, _) -> 
        { context = context; goal = Lollipop (f1, f2) }
    | ILL_Lollipop_left_proof (context, _, _, _, proof2) -> 
        (* The goal is the same as the goal of the second premise (Delta, B |- C) *)
        { context = context; goal = (get_conclusion_sequent proof2).goal }
    | ILL_Cut_proof (head_ctx, _, tail_ctx, _, proof2) ->
        (* The conclusion is the full context (head + tail) with the goal from second premise *)
        { context = head_ctx @ tail_ctx; goal = (get_conclusion_sequent proof2).goal }
    | ILL_Weakening_proof (context, exp_formula, goal_formula, _) ->
        (* Weakening adds !A to context: Γ,!A ⊢ B *)
        { context = context @ [exp_formula]; goal = goal_formula }
    | ILL_Contraction_proof (context, exp_formula, goal_formula, _) ->
        (* Contraction removes one copy of !A: Γ,!A ⊢ B *)
        { context = context @ [exp_formula]; goal = goal_formula }
    | ILL_Dereliction_proof (context, exp_formula, goal_formula, _) ->
        (* Dereliction removes ! from context: Γ,!A ⊢ B *)
        { context = context @ [exp_formula]; goal = goal_formula }
    | ILL_Promotion_proof (context, goal_formula, _) ->
        (* Promotion adds ! to goal: !Γ ⊢ !A *)
        { context = context; goal = goal_formula }
    | ILL_Hypothesis_proof sequent -> 
        sequent

(* Get all immediate sub-proofs (premises) of a proof tree node.
   @param proof - ILL proof tree
   @return ill_proof list - List of premise proofs
*)
let get_premises = function
    | ILL_Axiom_proof _ -> []
    | ILL_One_proof -> []
    | ILL_Top_proof _ -> []
    | ILL_Tensor_proof (_, _, _, p1, p2) -> [p1; p2]
    | ILL_Tensor_left_proof (_, _, _, p) -> [p]
    | ILL_With_left_1_proof (_, _, p) -> [p]
    | ILL_With_left_2_proof (_, _, p) -> [p]
    | ILL_With_right_proof (_, _, _, p1, p2) -> [p1; p2]
    | ILL_Plus_left_proof (_, _, _, p1, p2) -> [p1; p2]
    | ILL_Plus_right_1_proof (_, _, _, p) -> [p]
    | ILL_Plus_right_2_proof (_, _, _, p) -> [p]
    | ILL_Lollipop_proof (_, _, _, p) -> [p]
    | ILL_Lollipop_left_proof (_, _, _, p1, p2) -> [p1; p2]
    | ILL_Cut_proof (_, _, _, p1, p2) -> [p1; p2]
    | ILL_Weakening_proof (_, _, _, p) -> [p]
    | ILL_Contraction_proof (_, _, _, p) -> [p]
    | ILL_Dereliction_proof (_, _, _, p) -> [p]
    | ILL_Promotion_proof (_, _, p) -> [p]
    | ILL_Hypothesis_proof _ -> []

(* Replace the premises of a proof tree with new sub-proofs.
   Used for proof tree construction and manipulation.
   @param proof - Original proof tree
   @param new_premises - List of new sub-proofs
   @return ill_proof - Updated proof tree
*)
let set_premises proof new_premises = match proof, new_premises with
    | ILL_Axiom_proof _, [] -> proof
    | ILL_One_proof, [] -> proof
    | ILL_Top_proof _, [] -> proof
    | ILL_Tensor_proof (ctx, f1, f2, _, _), [p1; p2] -> ILL_Tensor_proof (ctx, f1, f2, p1, p2)
    | ILL_Tensor_left_proof (ctx, f1, f2, _), [p] -> ILL_Tensor_left_proof (ctx, f1, f2, p)
    | ILL_With_left_1_proof (ctx, f, _), [p] -> ILL_With_left_1_proof (ctx, f, p)
    | ILL_With_left_2_proof (ctx, f, _), [p] -> ILL_With_left_2_proof (ctx, f, p)
    | ILL_With_right_proof (ctx, f1, f2, _, _), [p1; p2] -> ILL_With_right_proof (ctx, f1, f2, p1, p2)
    | ILL_Plus_left_proof (ctx, f1, f2, _, _), [p1; p2] -> ILL_Plus_left_proof (ctx, f1, f2, p1, p2)
    | ILL_Plus_right_1_proof (ctx, f1, f2, _), [p] -> ILL_Plus_right_1_proof (ctx, f1, f2, p)
    | ILL_Plus_right_2_proof (ctx, f1, f2, _), [p] -> ILL_Plus_right_2_proof (ctx, f1, f2, p)
    | ILL_Lollipop_proof (ctx, f1, f2, _), [p] -> ILL_Lollipop_proof (ctx, f1, f2, p)
    | ILL_Lollipop_left_proof (ctx, f1, f2, _, _), [p1; p2] -> ILL_Lollipop_left_proof (ctx, f1, f2, p1, p2)
    | ILL_Cut_proof (head_ctx, f, tail_ctx, _, _), [p1; p2] -> ILL_Cut_proof (head_ctx, f, tail_ctx, p1, p2)
    | ILL_Weakening_proof (ctx, exp_f, goal_f, _), [p] -> ILL_Weakening_proof (ctx, exp_f, goal_f, p)
    | ILL_Contraction_proof (ctx, exp_f, goal_f, _), [p] -> ILL_Contraction_proof (ctx, exp_f, goal_f, p)
    | ILL_Dereliction_proof (ctx, exp_f, goal_f, _), [p] -> ILL_Dereliction_proof (ctx, exp_f, goal_f, p)
    | ILL_Promotion_proof (ctx, goal_f, _), [p] -> ILL_Promotion_proof (ctx, goal_f, p)
    | ILL_Hypothesis_proof _, [] -> proof
    | _ -> raise (ILL_Proof_Exception (false, "Invalid premise count for proof type"))

(* Extract the rule request information from a proof tree node.
   This reconstructs the rule that was applied to create this proof step.
   @param proof - ILL proof tree node
   @return ill_rule_request - Rule request that created this proof
   @raises ILL_Proof_Exception for hypothesis proofs (no applied rule)
*)
let get_rule_request proof =
    let open Ill_rule_request in
    match proof with
    | ILL_Axiom_proof _ -> 
        { rule = ILL_Axiom; formula_position = None; side = None; 
          context_split = None; sequent_side = None; cut_formula = None; cut_position = None }
    
    | ILL_One_proof -> 
        { rule = ILL_One; formula_position = None; side = None; 
          context_split = None; sequent_side = None; cut_formula = None; cut_position = None }
    
    | ILL_Top_proof _ -> 
        { rule = ILL_Top; formula_position = None; side = None; 
          context_split = None; sequent_side = None; cut_formula = None; cut_position = None }
    
    | ILL_Tensor_proof (_, _, _, _, _) -> 
        (* Context split information could be inferred but not stored in proof tree *)
        { rule = ILL_Tensor; formula_position = None; side = None; 
          context_split = None; sequent_side = None; cut_formula = None; cut_position = None }
    
    | ILL_Tensor_left_proof (_, _, _, _) -> 
        { rule = ILL_Tensor_left; formula_position = None; side = None; 
          context_split = None; sequent_side = None; cut_formula = None; cut_position = None }
    
    | ILL_With_left_1_proof (_, _, _) -> 
        { rule = ILL_With_left_1; formula_position = None; side = None; 
          context_split = None; sequent_side = None; cut_formula = None; cut_position = None }
    
    | ILL_With_left_2_proof (_, _, _) -> 
        { rule = ILL_With_left_2; formula_position = None; side = None; 
          context_split = None; sequent_side = None; cut_formula = None; cut_position = None }
    
    | ILL_With_right_proof (_, _, _, _, _) -> 
        { rule = ILL_With_right; formula_position = None; side = None; 
          context_split = None; sequent_side = None; cut_formula = None; cut_position = None }
    
    | ILL_Plus_left_proof (_, _, _, _, _) -> 
        { rule = ILL_Plus_left; formula_position = None; side = None; 
          context_split = None; sequent_side = None; cut_formula = None; cut_position = None }
    
    | ILL_Plus_right_1_proof (_, _, _, _) -> 
        { rule = ILL_Plus_right_1; formula_position = None; side = None; 
          context_split = None; sequent_side = None; cut_formula = None; cut_position = None }
    
    | ILL_Plus_right_2_proof (_, _, _, _) -> 
        { rule = ILL_Plus_right_2; formula_position = None; side = None; 
          context_split = None; sequent_side = None; cut_formula = None; cut_position = None }
    
    | ILL_Lollipop_proof (_, _, _, _) -> 
        { rule = ILL_Lollipop; formula_position = None; side = None; 
          context_split = None; sequent_side = None; cut_formula = None; cut_position = None }
    
    | ILL_Lollipop_left_proof (_, _, _, _, _) -> 
        { rule = ILL_Lollipop_left; formula_position = None; side = None; 
          context_split = None; sequent_side = None; cut_formula = None; cut_position = None }
    
    | ILL_Cut_proof (_, cut_f, _, _, _) -> 
        { rule = ILL_Cut; formula_position = None; side = None; 
          context_split = None; sequent_side = None; cut_formula = Some cut_f; cut_position = None }
    
    | ILL_Weakening_proof (_, _, _, _) -> 
        { rule = ILL_Weakening; formula_position = None; side = None; 
          context_split = None; sequent_side = None; cut_formula = None; cut_position = None }
    
    | ILL_Contraction_proof (_, _, _, _) -> 
        { rule = ILL_Contraction; formula_position = None; side = None; 
          context_split = None; sequent_side = None; cut_formula = None; cut_position = None }
    
    | ILL_Dereliction_proof (_, _, _, _) -> 
        { rule = ILL_Dereliction; formula_position = None; side = None; 
          context_split = None; sequent_side = None; cut_formula = None; cut_position = None }
    
    | ILL_Promotion_proof (_, _, _) -> 
        { rule = ILL_Promotion; formula_position = None; side = None; 
          context_split = None; sequent_side = None; cut_formula = None; cut_position = None }
    
    | ILL_Hypothesis_proof _ -> 
        raise (ILL_Proof_Exception (false, "Cannot get rule request from hypothesis proof"))

(* PROOF CONSTRUCTION FROM RULE REQUESTS *)

(* Apply an ILL inference rule to create a new proof tree.
   This is the main entry point called by the rule application system.
   @param sequent - The sequent to apply the rule to
   @param notations - User-defined formula notations
   @param rule_request - The specific rule to apply
   @return ill_proof - New proof tree with rule applied
*)
let from_sequent_and_rule_request sequent _notations _rule_request =
    (* TODO: Implement ILL rule application logic *)
    (* For now, just return a hypothesis proof as a stub *)
    let ill_seq = sequent_list_to_ill_sequent sequent in
    ILL_Hypothesis_proof ill_seq

(* Reconstruct ILL proof tree from sequent, rule request, and premise proofs.
   This is used when parsing JSON proof data from the frontend.
   @param ill_seq - The conclusion sequent of this proof step
   @param rule_request - The rule that was applied
   @param premises - List of premise proofs
   @return ill_proof - Reconstructed proof tree
*)
and from_sequent_and_rule_request_and_premises ill_seq rule_request premises =
    let open Ill_rule_request in
    match rule_request.rule, premises with
    
    (* Rules with no premises *)
    | ILL_Axiom, [] ->
        (match ill_seq.context, ill_seq.goal with
         | [Litt a], Litt b when a = b -> ILL_Axiom_proof a
         | _ -> raise (ILL_Proof_Exception (false, "Invalid axiom: context and goal must match")))
    
    | ILL_One, [] ->
        (match ill_seq.context, ill_seq.goal with
         | [], One -> ILL_One_proof
         | _ -> raise (ILL_Proof_Exception (false, "Invalid one rule: context must be empty and goal must be 1")))
    
    | ILL_Top, [] ->
        (match ill_seq.goal with
         | Top -> ILL_Top_proof ill_seq.context
         | _ -> raise (ILL_Proof_Exception (false, "Invalid top rule: goal must be ⊤")))
    
    (* Rules with one premise *)
    | ILL_Tensor_left, [premise] ->
        (match ill_seq.goal with
         | _ ->
             (* Extract tensor formula from context - simplified reconstruction *)
             (* In a full implementation, we would need to track which formula was the tensor *)
             let rec find_tensor_components ctx =
                 match ctx with
                 | Tensor (f1, f2) :: _ -> (f1, f2)
                 | _ :: rest -> find_tensor_components rest
                 | [] -> raise (ILL_Proof_Exception (false, "No tensor formula found in context"))
             in
             let (f1, f2) = find_tensor_components ill_seq.context in
             ILL_Tensor_left_proof (ill_seq.context, f1, f2, premise))
    
    | ILL_With_left_1, [premise] ->
        let rec find_with_components ctx =
            match ctx with
            | With (f1, f2) :: _ -> (f1, f2)
            | _ :: rest -> find_with_components rest
            | [] -> raise (ILL_Proof_Exception (false, "No with formula found in context"))
        in
        let (f1, f2) = find_with_components ill_seq.context in
        ILL_With_left_1_proof (ill_seq.context, With (f1, f2), premise)
    
    | ILL_With_left_2, [premise] ->
        let rec find_with_components ctx =
            match ctx with
            | With (f1, f2) :: _ -> (f1, f2)
            | _ :: rest -> find_with_components rest
            | [] -> raise (ILL_Proof_Exception (false, "No with formula found in context"))
        in
        let (f1, f2) = find_with_components ill_seq.context in
        ILL_With_left_2_proof (ill_seq.context, With (f1, f2), premise)
    
    | ILL_Plus_right_1, [premise] ->
        (match ill_seq.goal with
         | Plus (f1, f2) -> ILL_Plus_right_1_proof (ill_seq.context, f1, f2, premise)
         | _ -> raise (ILL_Proof_Exception (false, "Invalid plus right 1: goal must be A⊕B")))
    
    | ILL_Plus_right_2, [premise] ->
        (match ill_seq.goal with
         | Plus (f1, f2) -> ILL_Plus_right_2_proof (ill_seq.context, f1, f2, premise)
         | _ -> raise (ILL_Proof_Exception (false, "Invalid plus right 2: goal must be A⊕B")))
    
    | ILL_Lollipop, [premise] ->
        (match ill_seq.goal with
         | Lollipop (f1, f2) -> ILL_Lollipop_proof (ill_seq.context, f1, f2, premise)
         | _ -> raise (ILL_Proof_Exception (false, "Invalid lollipop: goal must be A⊸B")))
    
    (* Rules with two premises *)
    | ILL_Tensor, [premise1; premise2] ->
        (match ill_seq.goal with
         | Tensor (f1, f2) -> ILL_Tensor_proof (ill_seq.context, f1, f2, premise1, premise2)
         | _ -> raise (ILL_Proof_Exception (false, "Invalid tensor: goal must be A⊗B")))
    
    | ILL_With_right, [premise1; premise2] ->
        (match ill_seq.goal with
         | With (f1, f2) -> ILL_With_right_proof (ill_seq.context, f1, f2, premise1, premise2)
         | _ -> raise (ILL_Proof_Exception (false, "Invalid with right: goal must be A&B")))
    
    | ILL_Plus_left, [premise1; premise2] ->
        let rec find_plus_components ctx =
            match ctx with
            | Plus (f1, f2) :: _ -> (f1, f2)
            | _ :: rest -> find_plus_components rest
            | [] -> raise (ILL_Proof_Exception (false, "No plus formula found in context"))
        in
        let (f1, f2) = find_plus_components ill_seq.context in
        ILL_Plus_left_proof (ill_seq.context, f1, f2, premise1, premise2)
    
    | ILL_Lollipop_left, [premise1; premise2] ->
        let rec find_lollipop_components ctx =
            match ctx with
            | Lollipop (f1, f2) :: _ -> (f1, f2)
            | _ :: rest -> find_lollipop_components rest
            | [] -> raise (ILL_Proof_Exception (false, "No lollipop formula found in context"))
        in
        let (f1, f2) = find_lollipop_components ill_seq.context in
        ILL_Lollipop_left_proof (ill_seq.context, f1, f2, premise1, premise2)
    
    | ILL_Cut, [premise1; premise2] ->
        (* For cut, we need the cut formula from the rule request *)
        (match rule_request.cut_formula with
         | Some cut_f -> 
             (* Simple reconstruction - in practice, context splitting would be more complex *)
             let cut_pos = Option.value rule_request.cut_position ~default:0 in
             let (head_ctx, tail_ctx) = 
                 let rec split acc n lst =
                     match n, lst with
                     | 0, rest -> (List.rev acc, rest)
                     | n, h :: t when n > 0 -> split (h :: acc) (n - 1) t
                     | _ -> (List.rev acc, lst)
                 in
                 split [] cut_pos ill_seq.context
             in
             ILL_Cut_proof (head_ctx, cut_f, tail_ctx, premise1, premise2)
         | None -> raise (ILL_Proof_Exception (false, "Cut rule requires cut formula")))
    
    (* Invalid combinations *)
    | rule, prems -> 
        let rule_name = Ill_rule_request.rule_name rule in
        let premise_count = List.length prems in
        raise (ILL_Proof_Exception (false, 
            Printf.sprintf "Invalid premise count for rule %s: expected specific count, got %d" 
            rule_name premise_count))

(* PROOF VALIDATION *)

(* Check if a proof tree is complete (no open hypotheses).
   @param proof - ILL proof tree to check
   @return bool - True if proof is complete
*)
let rec is_complete_proof = function
    | ILL_Hypothesis_proof _ -> false  (* Open hypothesis *)
    | ILL_Axiom_proof _ -> true
    | ILL_One_proof -> true
    | ILL_Top_proof _ -> true
    | ILL_Tensor_proof (_, _, _, p1, p2) -> is_complete_proof p1 && is_complete_proof p2
    | ILL_Tensor_left_proof (_, _, _, p) -> is_complete_proof p
    | ILL_With_left_1_proof (_, _, p) -> is_complete_proof p
    | ILL_With_left_2_proof (_, _, p) -> is_complete_proof p
    | ILL_With_right_proof (_, _, _, p1, p2) -> is_complete_proof p1 && is_complete_proof p2
    | ILL_Plus_left_proof (_, _, _, p1, p2) -> is_complete_proof p1 && is_complete_proof p2
    | ILL_Plus_right_1_proof (_, _, _, p) -> is_complete_proof p
    | ILL_Plus_right_2_proof (_, _, _, p) -> is_complete_proof p
    | ILL_Lollipop_proof (_, _, _, p) -> is_complete_proof p
    | ILL_Lollipop_left_proof (_, _, _, p1, p2) -> is_complete_proof p1 && is_complete_proof p2
    | ILL_Cut_proof (_, _, _, p1, p2) -> is_complete_proof p1 && is_complete_proof p2
    | ILL_Weakening_proof (_, _, _, p) -> is_complete_proof p
    | ILL_Contraction_proof (_, _, _, p) -> is_complete_proof p
    | ILL_Dereliction_proof (_, _, _, p) -> is_complete_proof p
    | ILL_Promotion_proof (_, _, p) -> is_complete_proof p

(* Check if a proof tree is valid (rules correctly applied).
   @param proof - ILL proof tree to validate
   @return bool - True if proof is valid
*)
let rec is_valid_proof proof =
    (* TODO: Implement detailed proof validation *)
    (* For now, just check structural validity *)
    match proof with
    | ILL_Hypothesis_proof _ -> true  (* Hypotheses are always valid *)
    | ILL_Axiom_proof _ -> true       (* TODO: Check axiom validity *)
    | ILL_One_proof -> true
    | ILL_Top_proof _ -> true
    | ILL_Tensor_proof (_, _, _, p1, p2) -> is_valid_proof p1 && is_valid_proof p2
    | ILL_Tensor_left_proof (_, _, _, p) -> is_valid_proof p
    | ILL_With_left_1_proof (_, _, p) -> is_valid_proof p
    | ILL_With_left_2_proof (_, _, p) -> is_valid_proof p
    | ILL_With_right_proof (_, _, _, p1, p2) -> is_valid_proof p1 && is_valid_proof p2
    | ILL_Plus_left_proof (_, _, _, p1, p2) -> is_valid_proof p1 && is_valid_proof p2
    | ILL_Plus_right_1_proof (_, _, _, p) -> is_valid_proof p
    | ILL_Plus_right_2_proof (_, _, _, p) -> is_valid_proof p
    | ILL_Lollipop_proof (_, _, _, p) -> is_valid_proof p
    | ILL_Lollipop_left_proof (_, _, _, p1, p2) -> is_valid_proof p1 && is_valid_proof p2
    | ILL_Cut_proof (_, _, _, p1, p2) -> is_valid_proof p1 && is_valid_proof p2
    | ILL_Weakening_proof (_, _, _, p) -> is_valid_proof p
    | ILL_Contraction_proof (_, _, _, p) -> is_valid_proof p
    | ILL_Dereliction_proof (_, _, _, p) -> is_valid_proof p
    | ILL_Promotion_proof (_, _, p) -> is_valid_proof p

(* JSON SERIALIZATION *)

(* Convert ILL sequent to raw sequent format for JSON serialization.
   @param ill_seq - ILL sequent
   @return Raw_sequent.raw_sequent - Raw sequent representation
*)
let ill_sequent_to_raw_sequent ill_seq =
    let rec ill_formula_to_raw = function
        | One -> Raw_sequent.One
        | Top -> Raw_sequent.Top
        | Litt s -> Raw_sequent.Litt s
        | Tensor (f1, f2) -> Raw_sequent.Tensor (ill_formula_to_raw f1, ill_formula_to_raw f2)
        | With (f1, f2) -> Raw_sequent.With (ill_formula_to_raw f1, ill_formula_to_raw f2)
        | Plus (f1, f2) -> Raw_sequent.Plus (ill_formula_to_raw f1, ill_formula_to_raw f2)
        | Lollipop (f1, f2) -> Raw_sequent.Lollipop (ill_formula_to_raw f1, ill_formula_to_raw f2)
        | Ofcourse f -> Raw_sequent.Ofcourse (ill_formula_to_raw f)
    in
    let raw_context = List.map ill_formula_to_raw ill_seq.context in
    let raw_goal = ill_formula_to_raw ill_seq.goal in
    { Raw_sequent.hyp = raw_context; cons = [raw_goal] }

(* Convert ILL proof tree to JSON representation for frontend.
   @param proof - ILL proof tree
   @return Yojson.Basic.t - JSON representation
*)
let rec to_json proof =
    let get_sequent_json proof =
        let ill_seq = get_conclusion_sequent proof in
        let raw_seq = ill_sequent_to_raw_sequent ill_seq in
        Raw_sequent.to_json raw_seq
    in
    
    match proof with
    | ILL_Hypothesis_proof _ill_seq ->
        `Assoc [
            ("sequent", get_sequent_json proof);
            ("appliedRule", `Null)
        ]
    | _ ->
        (* For non-hypothesis proofs, include proper rule information *)
        let premises_json = List.map to_json (get_premises proof) in
        let rule_request = get_rule_request proof in
        let rule_request_json = Ill_rule_request.to_json rule_request in
        let applied_rule_json = `Assoc [
            ("ruleRequest", rule_request_json);
            ("premises", `List premises_json)
        ] in
        `Assoc [
            ("sequent", get_sequent_json proof);
            ("appliedRule", applied_rule_json)
        ]

(* Parse ILL proof tree from JSON representation.
   @param json - JSON representation from frontend
   @return ill_proof - Parsed ILL proof tree
*)
let rec from_json json =
    (* Extract sequent from JSON *)
    let sequent_json = Yojson.Basic.Util.member "sequent" json in
    let raw_seq = Raw_sequent.from_json sequent_json in
    
    (* Convert raw sequent to ILL sequent *)
    let rec raw_to_ill_formula = function
        | Raw_sequent.One -> One
        | Raw_sequent.Top -> Top
        | Raw_sequent.Litt s -> Litt s
        | Raw_sequent.Tensor (f1, f2) -> Tensor (raw_to_ill_formula f1, raw_to_ill_formula f2)
        | Raw_sequent.With (f1, f2) -> With (raw_to_ill_formula f1, raw_to_ill_formula f2)
        | Raw_sequent.Plus (f1, f2) -> Plus (raw_to_ill_formula f1, raw_to_ill_formula f2)
        | Raw_sequent.Lollipop (f1, f2) -> Lollipop (raw_to_ill_formula f1, raw_to_ill_formula f2)
        | _ -> raise (ILL_Proof_Exception (false, "Invalid formula type for ILL"))
    in
    
    let context = List.map raw_to_ill_formula raw_seq.hyp in
    let goal = match raw_seq.cons with
        | [g] -> raw_to_ill_formula g
        | _ -> raise (ILL_Proof_Exception (false, "ILL sequent must have exactly one conclusion"))
    in
    
    let ill_seq = { context = context; goal = goal } in
    
    (* Check if there's an applied rule *)
    let applied_rule_json = Yojson.Basic.Util.member "appliedRule" json in
    if applied_rule_json = `Null then
        ILL_Hypothesis_proof ill_seq
    else
        (* Parse rule request and premises to reconstruct proof tree *)
        let rule_request_json = Yojson.Basic.Util.member "ruleRequest" applied_rule_json in
        let rule_request = Ill_rule_request.from_json rule_request_json in
        let premises_json = Yojson.Basic.Util.member "premises" applied_rule_json in
        let premises_list = Yojson.Basic.Util.to_list premises_json in
        let premises = List.map from_json premises_list in
        
        (* Reconstruct the proof tree based on the rule and premises *)
        from_sequent_and_rule_request_and_premises ill_seq rule_request premises

(* PROOF STATISTICS *)

(* Count the number of inference rules used in a proof.
   @param proof - ILL proof tree
   @return int - Number of inference rule applications
*)
let rec count_inference_rules = function
    | ILL_Hypothesis_proof _ -> 0
    | ILL_Axiom_proof _ -> 1
    | ILL_One_proof -> 1
    | ILL_Top_proof _ -> 1
    | ILL_Tensor_proof (_, _, _, p1, p2) -> 1 + count_inference_rules p1 + count_inference_rules p2
    | ILL_Tensor_left_proof (_, _, _, p) -> 1 + count_inference_rules p
    | ILL_With_left_1_proof (_, _, p) -> 1 + count_inference_rules p
    | ILL_With_left_2_proof (_, _, p) -> 1 + count_inference_rules p
    | ILL_With_right_proof (_, _, _, p1, p2) -> 1 + count_inference_rules p1 + count_inference_rules p2
    | ILL_Plus_left_proof (_, _, _, p1, p2) -> 1 + count_inference_rules p1 + count_inference_rules p2
    | ILL_Plus_right_1_proof (_, _, _, p) -> 1 + count_inference_rules p
    | ILL_Plus_right_2_proof (_, _, _, p) -> 1 + count_inference_rules p
    | ILL_Lollipop_proof (_, _, _, p) -> 1 + count_inference_rules p
    | ILL_Lollipop_left_proof (_, _, _, p1, p2) -> 1 + count_inference_rules p1 + count_inference_rules p2
    | ILL_Cut_proof (_, _, _, p1, p2) -> 1 + count_inference_rules p1 + count_inference_rules p2
    | ILL_Weakening_proof (_, _, _, p) -> 1 + count_inference_rules p
    | ILL_Contraction_proof (_, _, _, p) -> 1 + count_inference_rules p
    | ILL_Dereliction_proof (_, _, _, p) -> 1 + count_inference_rules p
    | ILL_Promotion_proof (_, _, p) -> 1 + count_inference_rules p

(* Count the number of open hypotheses in a proof.
   @param proof - ILL proof tree  
   @return int - Number of unproven goals
*)
let rec count_open_hypotheses = function
    | ILL_Hypothesis_proof _ -> 1
    | ILL_Axiom_proof _ -> 0
    | ILL_One_proof -> 0
    | ILL_Top_proof _ -> 0
    | ILL_Tensor_proof (_, _, _, p1, p2) -> count_open_hypotheses p1 + count_open_hypotheses p2
    | ILL_Tensor_left_proof (_, _, _, p) -> count_open_hypotheses p
    | ILL_With_left_1_proof (_, _, p) -> count_open_hypotheses p
    | ILL_With_left_2_proof (_, _, p) -> count_open_hypotheses p
    | ILL_With_right_proof (_, _, _, p1, p2) -> count_open_hypotheses p1 + count_open_hypotheses p2
    | ILL_Plus_left_proof (_, _, _, p1, p2) -> count_open_hypotheses p1 + count_open_hypotheses p2
    | ILL_Plus_right_1_proof (_, _, _, p) -> count_open_hypotheses p
    | ILL_Plus_right_2_proof (_, _, _, p) -> count_open_hypotheses p
    | ILL_Lollipop_proof (_, _, _, p) -> count_open_hypotheses p
    | ILL_Lollipop_left_proof (_, _, _, p1, p2) -> count_open_hypotheses p1 + count_open_hypotheses p2
    | ILL_Cut_proof (_, _, _, p1, p2) -> count_open_hypotheses p1 + count_open_hypotheses p2
    | ILL_Weakening_proof (_, _, _, p) -> count_open_hypotheses p
    | ILL_Contraction_proof (_, _, _, p) -> count_open_hypotheses p
    | ILL_Dereliction_proof (_, _, _, p) -> count_open_hypotheses p
    | ILL_Promotion_proof (_, _, p) -> count_open_hypotheses p