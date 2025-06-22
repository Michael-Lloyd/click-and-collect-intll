(* INTUITIONISTIC LINEAR LOGIC RULE APPLICATION MODULE
   
   This module handles the application of ILL inference rules to sequents.
   It's the core of the interactive proof construction system for ILL.
   
   When users click on formulas in the frontend, this module:
   1. Parses the rule request from JSON
   2. Validates that the rule can be applied
   3. Applies the rule to generate new proof tree
   4. Returns the updated proof structure
   
   Key differences from classical LL rule application:
   - Only handles ILL rules (no exponentials, no ⅋, no &)
   - Works with asymmetric sequents (Γ ⊢ A)
   - Simpler context management (no complex permutations)
*)

open Ill_sequent
open Ill_proof
open Ill_rule_request

(* Exception for rule application errors *)
exception ILL_Rule_Application_Exception of bool * string;;

(* ILL CONSTRAINT VALIDATION AND PARSING *)

(* Convert raw sequent (from JSON) to ILL sequent format.
   @param raw_seq - Raw sequent from JSON parsing
   @return ill_sequent - Converted ILL sequent
   @raises ILL_Rule_Application_Exception for invalid ILL sequent
*)
let rec convert_raw_sequent_to_ill raw_seq =
    try
        (* Convert raw formulas to ILL formulas *)
        let context_formulas = List.map convert_raw_formula_to_ill raw_seq.Raw_sequent.hyp in
        let conclusion_formulas = List.map convert_raw_formula_to_ill raw_seq.Raw_sequent.cons in
        
        (* ILL requires exactly one conclusion *)
        match conclusion_formulas with
        | [] ->
            raise (ILL_Rule_Application_Exception (true, "ILL sequent must have exactly one conclusion"))
        | [goal] ->
            { context = context_formulas; goal = goal }
        | _ ->
            raise (ILL_Rule_Application_Exception (true, "ILL sequent can have only one conclusion formula"))
    with
    | ILL_Rule_Application_Exception (_, _) as e -> raise e
    | _ -> raise (ILL_Rule_Application_Exception (false, "Failed to convert raw sequent to ILL"))

(* Convert raw formula to ILL formula.
   @param raw_formula - Raw formula from JSON
   @return formula - ILL formula
   @raises ILL_Rule_Application_Exception for non-ILL connectives
*)
and convert_raw_formula_to_ill = function
    | Raw_sequent.One -> One
    | Raw_sequent.Top -> Top
    | Raw_sequent.Litt s -> Litt s
    | Raw_sequent.Tensor (f1, f2) -> 
        Tensor (convert_raw_formula_to_ill f1, convert_raw_formula_to_ill f2)
    | Raw_sequent.Plus (f1, f2) -> 
        Plus (convert_raw_formula_to_ill f1, convert_raw_formula_to_ill f2)
    | Raw_sequent.Lollipop (f1, f2) ->
        Lollipop (convert_raw_formula_to_ill f1, convert_raw_formula_to_ill f2)
    
    (* Invalid connectives for ILL *)
    | Raw_sequent.Bottom -> 
        raise (ILL_Rule_Application_Exception (true, "⊥ (bottom) is not allowed in ILL"))
    | Raw_sequent.Zero -> 
        raise (ILL_Rule_Application_Exception (true, "0 (zero) is not allowed in ILL"))
    | Raw_sequent.Dual _ -> 
        raise (ILL_Rule_Application_Exception (true, "^ (dual) is not allowed in ILL"))
    | Raw_sequent.Par (_, _) -> 
        raise (ILL_Rule_Application_Exception (true, "⅋ (par) is not allowed in ILL"))
    | Raw_sequent.With (f1, f2) ->
        With (convert_raw_formula_to_ill f1, convert_raw_formula_to_ill f2)
    | Raw_sequent.Ofcourse f -> 
        Ofcourse (convert_raw_formula_to_ill f)
    | Raw_sequent.Whynot _ -> 
        raise (ILL_Rule_Application_Exception (true, "? (why not) is not allowed in ILL"))

(* Validate that an ILL sequent satisfies all ILL constraints.
   @param ill_seq - ILL sequent to validate
   @raises ILL_Rule_Application_Exception for constraint violations
*)
and validate_ill_sequent_constraints ill_seq =
    (* ILL constraint: exactly one formula on the right-hand side *)
    validate_single_conclusion ill_seq;
    
    (* Validate that all formulas use only ILL connectives *)
    validate_ill_formulas_only ill_seq

(* Validate that sequent has exactly one conclusion (ILL constraint).
   @param ill_seq - ILL sequent to validate
   @raises ILL_Rule_Application_Exception if multiple conclusions
*)
and validate_single_conclusion _ill_seq =
    (* In our ILL sequent structure, we already enforce single conclusion by design *)
    (* The goal field contains exactly one formula *)
    ()

(* Validate that sequent uses only ILL connectives.
   @param ill_seq - ILL sequent to validate
   @raises ILL_Rule_Application_Exception for non-ILL connectives
*)
and validate_ill_formulas_only ill_seq =
    let rec validate_formula = function
        | One | Top | Litt _ -> ()
        | Tensor (f1, f2) | With (f1, f2) | Plus (f1, f2) | Lollipop (f1, f2) ->
            validate_formula f1;
            validate_formula f2
        | Ofcourse f ->
            validate_formula f
    in
    List.iter validate_formula ill_seq.context;
    validate_formula ill_seq.goal

(* RULE APPLICATION CORE *)

(* Apply an ILL rule to a sequent with full error handling.
   This is the main entry point for rule application.
   @param request_as_json - JSON request from frontend
   @return ill_proof - New proof tree with rule applied
   @raises ILL_Rule_Application_Exception for invalid applications
*)
and apply_rule_with_exceptions request_as_json =
    try
        (* Extract rule request from JSON *)
        let rule_request_json = Request_utils.get_key request_as_json "ruleRequest" in
        let rule_request = from_json rule_request_json in
        
        (* Extract sequent from JSON and parse it using existing infrastructure *)
        let sequent_json = Request_utils.get_key request_as_json "sequent" in
        let raw_sequent = Raw_sequent.from_json sequent_json in
        let ill_sequent = convert_raw_sequent_to_ill raw_sequent in
        
        (* Validate ILL constraints *)
        validate_ill_sequent_constraints ill_sequent;
        
        (* Extract notations (if any) *)
        let notations = [] in  (* TODO: Parse notations properly *)
        
        (* Use intelligent rule selection only when rule is generic or ambiguous *)
        let final_rule_request = 
            match rule_request.rule with
            | ILL_With_left_1 | ILL_With_left_2 | ILL_Plus_right_1 | ILL_Plus_right_2 
            | ILL_Weakening | ILL_Contraction | ILL_Dereliction ->
                (* Frontend has already specified a specific rule, don't override it *)
                rule_request
            | _ ->
                (* Use intelligent rule selection for generic or ambiguous rules *)
                Ill_rule_request.infer_rule_from_side_and_formula rule_request ill_sequent
        in
        
        (* Apply the final rule *)
        apply_ill_rule_internal final_rule_request ill_sequent notations
        
    with
    | Request_utils.Bad_request_exception msg -> 
        raise (ILL_Rule_Application_Exception (false, "Bad request: " ^ msg))
    | ILL_Rule_Json_Exception msg -> 
        raise (ILL_Rule_Application_Exception (false, "Invalid rule JSON: " ^ msg))
    | Failure msg ->
        raise (ILL_Rule_Application_Exception (false, "Failure: " ^ msg))
    | Invalid_argument msg ->
        raise (ILL_Rule_Application_Exception (false, "Invalid argument: " ^ msg))
    | exn -> 
        raise (ILL_Rule_Application_Exception (false, "Unknown error: " ^ (Printexc.to_string exn)))

(* Apply a specific ILL rule to a sequent.
   @param rule_req - Parsed rule request
   @param ill_seq - ILL sequent to apply rule to  
   @param notations - User-defined notation list
   @return ill_proof - New proof tree
*)
and apply_ill_rule_internal rule_req ill_seq _notations =
    (* Validate that rule can be applied *)
    let can_apply, error_msg = Ill_rule_request.can_apply_rule rule_req.rule ill_seq in
    if not can_apply then
        raise (ILL_Rule_Application_Exception (true, error_msg));
    
    (* Apply the rule based on type *)
    match rule_req.rule with
    | ILL_Axiom ->
        apply_axiom_rule ill_seq
    | ILL_One_right ->
        apply_one_right_rule ill_seq
    | ILL_One_left ->
        apply_one_left_rule rule_req ill_seq
    | ILL_Top ->
        apply_top_rule ill_seq
    | ILL_Tensor ->
        apply_tensor_rule rule_req ill_seq
    | ILL_Tensor_left ->
        apply_tensor_left_rule rule_req ill_seq
    | ILL_With_left_1 ->
        apply_with_left_1_rule rule_req ill_seq
    | ILL_With_left_2 ->
        apply_with_left_2_rule rule_req ill_seq
    | ILL_With_right ->
        apply_with_right_rule ill_seq
    | ILL_Plus_left ->
        apply_plus_left_rule rule_req ill_seq
    | ILL_Plus_right_1 ->
        apply_plus_right_1_rule ill_seq
    | ILL_Plus_right_2 ->
        apply_plus_right_2_rule ill_seq
    | ILL_Lollipop ->
        apply_lollipop_rule ill_seq
    | ILL_Lollipop_left ->
        apply_lollipop_left_rule rule_req ill_seq
    | ILL_Cut ->
        apply_cut_rule rule_req ill_seq
    | ILL_Weakening ->
        apply_weakening_rule rule_req ill_seq
    | ILL_Contraction ->
        apply_contraction_rule rule_req ill_seq
    | ILL_Dereliction ->
        apply_dereliction_rule rule_req ill_seq
    | ILL_Promotion ->
        apply_promotion_rule rule_req ill_seq

(* INDIVIDUAL RULE IMPLEMENTATIONS *)

(* Apply ILL axiom rule: A ⊢ A
   @param ill_seq - Sequent with form [A] ⊢ A
   @return ill_proof - Axiom proof
*)
and apply_axiom_rule ill_seq =
    (* Validate ILL constraint: exactly one formula on RHS *)
    validate_single_conclusion ill_seq;
    
    match ill_seq.context, ill_seq.goal with
    | [Litt a], Litt b when a = b ->
        ILL_Axiom_proof a
    | _ ->
        raise (ILL_Rule_Application_Exception (true, "Axiom rule requires context A and goal A"))

(* Apply ILL one right rule: ⊢ 1
   @param ill_seq - Sequent with form [] ⊢ 1
   @return ill_proof - One right proof
*)
and apply_one_right_rule ill_seq =
    (* Validate ILL constraint: exactly one formula on RHS *)
    validate_single_conclusion ill_seq;
    
    match ill_seq.context, ill_seq.goal with
    | [], One ->
        ILL_One_right_proof
    | _ ->
        raise (ILL_Rule_Application_Exception (true, "One right rule requires empty context and goal 1"))

(* Apply ILL one left rule: Γ,1,Δ ⊢ A becomes Γ,Δ ⊢ A
   @param rule_req - Rule request with position information  
   @param ill_seq - Sequent with 1 in context
   @return ill_proof - One left proof
*)
and apply_one_left_rule rule_req ill_seq =
    (* Validate ILL constraint: exactly one formula on RHS *)
    validate_single_conclusion ill_seq;
    
    match rule_req.formula_position with
    | Some pos when pos >= 0 && pos < List.length ill_seq.context ->
        (* Use specific position if provided *)
        let context_list = ill_seq.context in
        let (before, at_pos, after) = split_list_at_position context_list pos in
        (match at_pos with
         | One ->
             let new_context = before @ after in
             let premise = { context = new_context; goal = ill_seq.goal } in
             
             validate_ill_sequent_constraints premise;
             let subproof = ILL_Hypothesis_proof premise in
             ILL_One_left_proof (ill_seq.context, subproof)
         | _ ->
             raise (ILL_Rule_Application_Exception (true, 
                 "Position " ^ string_of_int pos ^ " does not contain 1")))
    | _ ->
        (* Fallback to finding first 1 *)
        let rec find_and_remove_one acc = function
            | [] -> raise (ILL_Rule_Application_Exception (true, "One left rule requires 1 in context"))
            | One :: rest ->
                let new_context = acc @ rest in
                let premise = { context = new_context; goal = ill_seq.goal } in
                
                (* Validate that premise maintains ILL constraints *)
                validate_ill_sequent_constraints premise;
                
                let subproof = ILL_Hypothesis_proof premise in
                ILL_One_left_proof (ill_seq.context, subproof)
            | f :: rest -> find_and_remove_one (acc @ [f]) rest
        in
        find_and_remove_one [] ill_seq.context

(* Apply ILL top rule: Γ ⊢ ⊤
   @param ill_seq - Sequent with goal ⊤
   @return ill_proof - Top proof
*)
and apply_top_rule ill_seq =
    (* Validate ILL constraint: exactly one formula on RHS *)
    validate_single_conclusion ill_seq;
    
    match ill_seq.goal with
    | Top ->
        ILL_Top_proof ill_seq.context
    | _ ->
        raise (ILL_Rule_Application_Exception (true, "Top rule requires goal ⊤"))

(* Apply ILL tensor rule: Γ,Δ ⊢ A⊗B becomes Γ ⊢ A and Δ ⊢ B
   @param rule_req - Rule request with context split info
   @param ill_seq - Sequent with goal A⊗B
   @return ill_proof - Tensor proof with two premises
*)
and apply_tensor_rule rule_req ill_seq =
    (* Validate ILL constraint: exactly one formula on RHS *)
    validate_single_conclusion ill_seq;
    
    match ill_seq.goal with
    | Tensor (a, b) ->
        (* Split context between the two premises using comma selection if available *)
        let ctx1, ctx2 = Ill_rule_request.split_context_for_tensor ill_seq.context rule_req.context_split in
        let premise1 = { context = ctx1; goal = a } in
        let premise2 = { context = ctx2; goal = b } in
        
        (* Validate that both premises maintain ILL constraints *)
        validate_ill_sequent_constraints premise1;
        validate_ill_sequent_constraints premise2;
        
        let subproof1 = ILL_Hypothesis_proof premise1 in
        let subproof2 = ILL_Hypothesis_proof premise2 in
        ILL_Tensor_proof (ill_seq.context, a, b, subproof1, subproof2)
    | _ ->
        raise (ILL_Rule_Application_Exception (true, "Tensor rule requires goal A⊗B"))

(* Apply ILL tensor left rule: Γ,A⊗B,Δ ⊢ C becomes Γ,A,B,Δ ⊢ C
   @param rule_req - Rule request with position information
   @param ill_seq - Sequent with A⊗B in context
   @return ill_proof - Tensor left proof
*)
and apply_tensor_left_rule rule_req ill_seq =
    (* Validate ILL constraint: exactly one formula on RHS *)
    validate_single_conclusion ill_seq;
    
    match rule_req.formula_position with
    | Some pos when pos >= 0 && pos < List.length ill_seq.context ->
        (* Use specific position if provided *)
        let context_as_array = Array.of_list ill_seq.context in
        (match context_as_array.(pos) with
         | Tensor (a, b) ->
             (* Replace the tensor at position pos with its components *)
             let before = Array.sub context_as_array 0 pos in
             let after = Array.sub context_as_array (pos + 1) (Array.length context_as_array - pos - 1) in
             let new_context = Array.to_list before @ [a; b] @ Array.to_list after in
             let premise = { context = new_context; goal = ill_seq.goal } in
             
             validate_ill_sequent_constraints premise;
             let subproof = ILL_Hypothesis_proof premise in
             ILL_Tensor_left_proof (ill_seq.context, a, b, subproof)
         | _ ->
             raise (ILL_Rule_Application_Exception (true, 
                 "Position " ^ string_of_int pos ^ " does not contain a tensor formula")))
    | _ ->
        (* Fallback to finding first tensor (original behavior) *)
        let rec find_and_expand_tensor acc = function
            | [] -> raise (ILL_Rule_Application_Exception (true, "Tensor left rule requires A⊗B in context"))
            | Tensor (a, b) :: rest ->
                let new_context = acc @ [a; b] @ rest in
                let premise = { context = new_context; goal = ill_seq.goal } in
                
                (* Validate that premise maintains ILL constraints *)
                validate_ill_sequent_constraints premise;
                
                let subproof = ILL_Hypothesis_proof premise in
                ILL_Tensor_left_proof (ill_seq.context, a, b, subproof)
            | f :: rest -> find_and_expand_tensor (acc @ [f]) rest
        in
        find_and_expand_tensor [] ill_seq.context

(* Apply ILL with left 1 rule: Γ,A&B,Δ ⊢ C becomes Γ,A,Δ ⊢ C
   @param rule_req - Rule request with position information
   @param ill_seq - Sequent with A&B in context
   @return ill_proof - With left 1 proof
*)
and apply_with_left_1_rule rule_req ill_seq =
    (* Validate ILL constraint: exactly one formula on RHS *)
    validate_single_conclusion ill_seq;
    
    match rule_req.formula_position with
    | Some pos when pos >= 0 && pos < List.length ill_seq.context ->
        (* Use specific position if provided *)
        let context_list = ill_seq.context in
        let (before, at_pos, after) = split_list_at_position context_list pos in
        (match at_pos with
         | With (a, _) ->
             let new_context = before @ [a] @ after in
             let premise = { context = new_context; goal = ill_seq.goal } in
             
             validate_ill_sequent_constraints premise;
             let subproof = ILL_Hypothesis_proof premise in
             ILL_With_left_1_proof (ill_seq.context, a, subproof)
         | _ ->
             raise (ILL_Rule_Application_Exception (true, 
                 "Position " ^ string_of_int pos ^ " does not contain a with formula")))
    | _ ->
        (* Fallback to finding first with (original behavior) *)
        let rec find_and_extract_with acc = function
            | [] -> raise (ILL_Rule_Application_Exception (true, "With left 1 rule requires A&B in context"))
            | With (a, _) :: rest ->
                let new_context = acc @ [a] @ rest in
                let premise = { context = new_context; goal = ill_seq.goal } in
                
                (* Validate that premise maintains ILL constraints *)
                validate_ill_sequent_constraints premise;
                
                let subproof = ILL_Hypothesis_proof premise in
                ILL_With_left_1_proof (ill_seq.context, a, subproof)
            | f :: rest -> find_and_extract_with (acc @ [f]) rest
        in
        find_and_extract_with [] ill_seq.context

(* Apply ILL with left 2 rule: Γ,A&B,Δ ⊢ C becomes Γ,B,Δ ⊢ C
   @param rule_req - Rule request with position information
   @param ill_seq - Sequent with A&B in context
   @return ill_proof - With left 2 proof
*)
and apply_with_left_2_rule rule_req ill_seq =
    (* Validate ILL constraint: exactly one formula on RHS *)
    validate_single_conclusion ill_seq;
    
    match rule_req.formula_position with
    | Some pos when pos >= 0 && pos < List.length ill_seq.context ->
        (* Use specific position if provided *)
        let context_list = ill_seq.context in
        let (before, at_pos, after) = split_list_at_position context_list pos in
        (match at_pos with
         | With (_, b) ->
             let new_context = before @ [b] @ after in
             let premise = { context = new_context; goal = ill_seq.goal } in
             
             validate_ill_sequent_constraints premise;
             let subproof = ILL_Hypothesis_proof premise in
             ILL_With_left_2_proof (ill_seq.context, b, subproof)
         | _ ->
             raise (ILL_Rule_Application_Exception (true, 
                 "Position " ^ string_of_int pos ^ " does not contain a with formula")))
    | _ ->
        (* Fallback to finding first with (original behavior) *)
        let rec find_and_extract_with acc = function
            | [] -> raise (ILL_Rule_Application_Exception (true, "With left 2 rule requires A&B in context"))
            | With (_, b) :: rest ->
                let new_context = acc @ [b] @ rest in
                let premise = { context = new_context; goal = ill_seq.goal } in
                
                (* Validate that premise maintains ILL constraints *)
                validate_ill_sequent_constraints premise;
                
                let subproof = ILL_Hypothesis_proof premise in
                ILL_With_left_2_proof (ill_seq.context, b, subproof)
            | f :: rest -> find_and_extract_with (acc @ [f]) rest
        in
        find_and_extract_with [] ill_seq.context

(* Apply ILL with right rule: Γ ⊢ A&B becomes Γ ⊢ A and Γ ⊢ B
   @param ill_seq - Sequent with goal A&B
   @return ill_proof - With right proof with two premises
*)
and apply_with_right_rule ill_seq =
    (* Validate ILL constraint: exactly one formula on RHS *)
    validate_single_conclusion ill_seq;
    
    match ill_seq.goal with
    | With (a, b) ->
        let premise1 = { context = ill_seq.context; goal = a } in
        let premise2 = { context = ill_seq.context; goal = b } in
        
        (* Validate that both premises maintain ILL constraints *)
        validate_ill_sequent_constraints premise1;
        validate_ill_sequent_constraints premise2;
        
        let subproof1 = ILL_Hypothesis_proof premise1 in
        let subproof2 = ILL_Hypothesis_proof premise2 in
        ILL_With_right_proof (ill_seq.context, a, b, subproof1, subproof2)
    | _ ->
        raise (ILL_Rule_Application_Exception (true, "With right rule requires goal A&B"))

(* Apply ILL plus left rule: Γ,A⊕B,Δ ⊢ C becomes Γ,A,Δ ⊢ C and Γ,B,Δ ⊢ C
   @param rule_req - Rule request with position information
   @param ill_seq - Sequent with A⊕B in context
   @return ill_proof - Plus left proof with two premises
*)
and apply_plus_left_rule rule_req ill_seq =
    (* Validate ILL constraint: exactly one formula on RHS *)
    validate_single_conclusion ill_seq;
    
    match rule_req.formula_position with
    | Some pos when pos >= 0 && pos < List.length ill_seq.context ->
        (* Use specific position if provided *)
        let context_list = ill_seq.context in
        let (before, at_pos, after) = split_list_at_position context_list pos in
        (match at_pos with
         | Plus (a, b) ->
             let remaining_context = before @ after in
             let premise1 = { context = a :: remaining_context; goal = ill_seq.goal } in
             let premise2 = { context = b :: remaining_context; goal = ill_seq.goal } in
             
             validate_ill_sequent_constraints premise1;
             validate_ill_sequent_constraints premise2;
             
             let subproof1 = ILL_Hypothesis_proof premise1 in
             let subproof2 = ILL_Hypothesis_proof premise2 in
             ILL_Plus_left_proof (ill_seq.context, a, b, subproof1, subproof2)
         | _ ->
             raise (ILL_Rule_Application_Exception (true, 
                 "Position " ^ string_of_int pos ^ " does not contain a plus formula")))
    | _ ->
        (* Fallback to finding first plus (original behavior) *)
        let rec find_and_extract_plus acc = function
            | [] -> raise (ILL_Rule_Application_Exception (true, "Plus left rule requires A⊕B in context"))
            | Plus (a, b) :: rest ->
                let remaining_context = acc @ rest in
                let premise1 = { context = a :: remaining_context; goal = ill_seq.goal } in
                let premise2 = { context = b :: remaining_context; goal = ill_seq.goal } in
                
                (* Validate that both premises maintain ILL constraints *)
                validate_ill_sequent_constraints premise1;
                validate_ill_sequent_constraints premise2;
                
                let subproof1 = ILL_Hypothesis_proof premise1 in
                let subproof2 = ILL_Hypothesis_proof premise2 in
                ILL_Plus_left_proof (ill_seq.context, a, b, subproof1, subproof2)
            | f :: rest -> find_and_extract_plus (acc @ [f]) rest
        in
        find_and_extract_plus [] ill_seq.context

(* Apply ILL plus right 1 rule: Γ ⊢ A⊕B becomes Γ ⊢ A
   @param ill_seq - Sequent with goal A⊕B
   @return ill_proof - Plus right 1 proof
*)
and apply_plus_right_1_rule ill_seq =
    (* Validate ILL constraint: exactly one formula on RHS *)
    validate_single_conclusion ill_seq;
    
    match ill_seq.goal with
    | Plus (a, b) ->
        let premise = { context = ill_seq.context; goal = a } in
        
        (* Validate that premise maintains ILL constraints *)
        validate_ill_sequent_constraints premise;
        
        let subproof = ILL_Hypothesis_proof premise in
        ILL_Plus_right_1_proof (ill_seq.context, a, b, subproof)
    | _ ->
        raise (ILL_Rule_Application_Exception (true, "Plus right 1 rule requires goal A⊕B"))

(* Apply ILL plus right 2 rule: Γ ⊢ A⊕B becomes Γ ⊢ B
   @param ill_seq - Sequent with goal A⊕B
   @return ill_proof - Plus right 2 proof
*)
and apply_plus_right_2_rule ill_seq =
    (* Validate ILL constraint: exactly one formula on RHS *)
    validate_single_conclusion ill_seq;
    
    match ill_seq.goal with
    | Plus (a, b) ->
        let premise = { context = ill_seq.context; goal = b } in
        
        (* Validate that premise maintains ILL constraints *)
        validate_ill_sequent_constraints premise;
        
        let subproof = ILL_Hypothesis_proof premise in
        ILL_Plus_right_2_proof (ill_seq.context, a, b, subproof)
    | _ ->
        raise (ILL_Rule_Application_Exception (true, "Plus right 2 rule requires goal A⊕B"))

(* Apply ILL lollipop rule: Γ ⊢ A⊸B becomes Γ,A ⊢ B
   @param ill_seq - Sequent with goal A⊸B
   @return ill_proof - Lollipop proof
*)
and apply_lollipop_rule ill_seq =
    (* Validate ILL constraint: exactly one formula on RHS *)
    validate_single_conclusion ill_seq;
    
    match ill_seq.goal with
    | Lollipop (a, b) ->
        let premise = { context = ill_seq.context @ [a]; goal = b } in
        
        (* Validate that premise maintains ILL constraints *)
        validate_ill_sequent_constraints premise;
        
        let subproof = ILL_Hypothesis_proof premise in
        ILL_Lollipop_proof (ill_seq.context, a, b, subproof)
    | _ ->
        raise (ILL_Rule_Application_Exception (true, "Lollipop rule requires goal A⊸B"))

(* Apply ILL lollipop left rule: Γ,A⊸B,Δ ⊢ C becomes Γ ⊢ A and Δ,B ⊢ C
   @param rule_req - Rule request with position information
   @param ill_seq - Sequent with A⊸B in context
   @return ill_proof - Lollipop left proof with two premises
*)
and apply_lollipop_left_rule rule_req ill_seq =
    (* Validate ILL constraint: exactly one formula on RHS *)
    validate_single_conclusion ill_seq;
    
    match rule_req.formula_position with
    | Some pos when pos >= 0 && pos < List.length ill_seq.context ->
        (* Use specific position if provided *)
        let context_list = ill_seq.context in
        let (before, at_pos, after) = split_list_at_position context_list pos in
        (match at_pos with
         | Lollipop (a, b) ->
             (* According to CLAUDE.md: Gamma |- A <gap> Delta, B |- C / Gamma, A -o B, Delta |- C *)
             let premise1 = { context = before; goal = a } in
             let premise2 = { context = after @ [b]; goal = ill_seq.goal } in
             
             validate_ill_sequent_constraints premise1;
             validate_ill_sequent_constraints premise2;
             
             let subproof1 = ILL_Hypothesis_proof premise1 in
             let subproof2 = ILL_Hypothesis_proof premise2 in
             ILL_Lollipop_left_proof (ill_seq.context, a, b, subproof1, subproof2)
         | _ ->
             raise (ILL_Rule_Application_Exception (true, 
                 "Position " ^ string_of_int pos ^ " does not contain a lollipop formula")))
    | _ ->
        (* Fallback to finding first lollipop - split context appropriately *)
        let rec find_and_extract_lollipop acc = function
            | [] -> raise (ILL_Rule_Application_Exception (true, "Lollipop left rule requires A⊸B in context"))
            | Lollipop (a, b) :: rest ->
                (* Use acc as Gamma, rest as Delta *)
                let premise1 = { context = acc; goal = a } in
                let premise2 = { context = rest @ [b]; goal = ill_seq.goal } in
                
                (* Validate that both premises maintain ILL constraints *)
                validate_ill_sequent_constraints premise1;
                validate_ill_sequent_constraints premise2;
                
                let subproof1 = ILL_Hypothesis_proof premise1 in
                let subproof2 = ILL_Hypothesis_proof premise2 in
                ILL_Lollipop_left_proof (ill_seq.context, a, b, subproof1, subproof2)
            | f :: rest -> find_and_extract_lollipop (acc @ [f]) rest
        in
        find_and_extract_lollipop [] ill_seq.context

(* Apply ILL cut rule: Γ,Δ ⊢ C becomes Γ ⊢ A and Δ,A ⊢ C
   @param rule_req - Rule request with cut formula and position
   @param ill_seq - Sequent to apply cut to
   @return ill_proof - Cut proof with two premises
*)
and apply_cut_rule rule_req ill_seq =
    (* Validate ILL constraint: exactly one formula on RHS *)
    validate_single_conclusion ill_seq;
    
    (* Extract cut formula and position from rule request *)
    let cut_formula = match rule_req.cut_formula with
        | Some f -> f
        | None -> raise (ILL_Rule_Application_Exception (true, "Cut rule requires a cut formula"))
    in
    
    let cut_position = match rule_req.cut_position with
        | Some pos -> pos
        | None -> 0  (* Default to beginning of context *)
    in
    
    (* Split context at cut position *)
    let gamma, delta = 
        if cut_position < 0 || cut_position > List.length ill_seq.context then
            raise (ILL_Rule_Application_Exception (true, "Invalid cut position"))
        else
            let ctx_array = Array.of_list ill_seq.context in
            let gamma = Array.sub ctx_array 0 cut_position |> Array.to_list in
            let delta = Array.sub ctx_array cut_position (Array.length ctx_array - cut_position) |> Array.to_list in
            (gamma, delta)
    in
    
    (* Create the two premises *)
    let premise1 = { context = gamma; goal = cut_formula } in
    let premise2 = { context = delta @ [cut_formula]; goal = ill_seq.goal } in
    
    (* Validate that both premises maintain ILL constraints *)
    validate_ill_sequent_constraints premise1;
    validate_ill_sequent_constraints premise2;
    
    (* Create hypothesis proofs for the premises *)
    let subproof1 = ILL_Hypothesis_proof premise1 in
    let subproof2 = ILL_Hypothesis_proof premise2 in
    
    (* Return cut proof *)
    ILL_Cut_proof (gamma, cut_formula, delta, subproof1, subproof2)

(* Apply ILL weakening rule: Γ ⊢ B / Γ,!A ⊢ B
   @param rule_req - Rule request (contains position and exponential formula)
   @param ill_seq - Sequent with form Γ,!A ⊢ B
   @return ill_proof - Weakening proof
*)
and apply_weakening_rule rule_req ill_seq =
    (* Validate ILL constraint: exactly one formula on RHS *)
    validate_single_conclusion ill_seq;
    
    (* Extract formula position from rule request *)
    let formula_pos = match rule_req.formula_position with
        | Some pos -> pos
        | None -> raise (ILL_Rule_Application_Exception (true, "Weakening rule requires formula position"))
    in
    
    (* Split context to find the !A formula *)
    if formula_pos < 0 || formula_pos >= List.length ill_seq.context then
        raise (ILL_Rule_Application_Exception (true, "Invalid formula position for weakening rule"));
    
    let (gamma_before, exp_formula, gamma_after) = split_list_at_position ill_seq.context formula_pos in
    
    (* Validate that the formula at position is exponential *)
    (match exp_formula with
     | Ofcourse _ ->
         (* Construct premise sequent: Γ ⊢ B (without !A) *)
         let premise_context = gamma_before @ gamma_after in
         let premise = { context = premise_context; goal = ill_seq.goal } in
         
         (* Validate premise is well-formed *)
         validate_ill_sequent_constraints premise;
         
         (* Create hypothesis proof for premise *)
         let subproof = ILL_Hypothesis_proof premise in
         
         (* Return weakening proof *)
         ILL_Weakening_proof (ill_seq.context, exp_formula, ill_seq.goal, subproof)
         
     | _ -> raise (ILL_Rule_Application_Exception (true, "Weakening rule requires !A formula at specified position")))

(* Apply ILL contraction rule: Γ,!A ⊢ B / Γ,!A,!A ⊢ B
   @param rule_req - Rule request (contains position of !A formula)
   @param ill_seq - Sequent with form Γ,!A ⊢ B
   @return ill_proof - Contraction proof
*)
and apply_contraction_rule rule_req ill_seq =
    (* Validate ILL constraint: exactly one formula on RHS *)
    validate_single_conclusion ill_seq;
    
    (* Extract formula position from rule request *)
    let formula_pos = match rule_req.formula_position with
        | Some pos -> pos
        | None -> raise (ILL_Rule_Application_Exception (true, "Contraction rule requires formula position"))
    in
    
    (* Split context to find the !A formula *)
    if formula_pos < 0 || formula_pos >= List.length ill_seq.context then
        raise (ILL_Rule_Application_Exception (true, "Invalid formula position for contraction rule"));
    
    let (gamma_before, exp_formula, gamma_after) = split_list_at_position ill_seq.context formula_pos in
    
    (* Validate that the formula at position is exponential *)
    (match exp_formula with
     | Ofcourse _ ->
         (* Construct premise sequent: Γ,!A,!A ⊢ B (with duplicated !A) *)
         let premise_context = gamma_before @ [exp_formula; exp_formula] @ gamma_after in
         let premise = { context = premise_context; goal = ill_seq.goal } in
         
         (* Validate premise is well-formed *)
         validate_ill_sequent_constraints premise;
         
         (* Create hypothesis proof for premise *)
         let subproof = ILL_Hypothesis_proof premise in
         
         (* Return contraction proof *)
         ILL_Contraction_proof (gamma_before @ gamma_after, exp_formula, ill_seq.goal, subproof)
         
     | _ -> raise (ILL_Rule_Application_Exception (true, "Contraction rule requires !A formula at specified position")))

(* Apply ILL dereliction rule: Γ,!A ⊢ B / Γ,A ⊢ B
   @param rule_req - Rule request (contains position of !A formula)
   @param ill_seq - Sequent with form Γ,!A ⊢ B
   @return ill_proof - Dereliction proof
*)
and apply_dereliction_rule rule_req ill_seq =
    (* Validate ILL constraint: exactly one formula on RHS *)
    validate_single_conclusion ill_seq;
    
    (* Extract formula position from rule request *)
    let formula_pos = match rule_req.formula_position with
        | Some pos -> pos
        | None -> raise (ILL_Rule_Application_Exception (true, "Dereliction rule requires formula position"))
    in
    
    (* Split context to find the !A formula *)
    if formula_pos < 0 || formula_pos >= List.length ill_seq.context then
        raise (ILL_Rule_Application_Exception (true, "Invalid formula position for dereliction rule"));
    
    let (gamma_before, exp_formula, gamma_after) = split_list_at_position ill_seq.context formula_pos in
    
    (* Validate that the formula at position is exponential *)
    (match exp_formula with
     | Ofcourse inner_formula ->
         (* Construct premise sequent: Γ,A ⊢ B (with A instead of !A) *)
         let premise_context = gamma_before @ [inner_formula] @ gamma_after in
         let premise = { context = premise_context; goal = ill_seq.goal } in
         
         (* Validate premise is well-formed *)
         validate_ill_sequent_constraints premise;
         
         (* Create hypothesis proof for premise *)
         let subproof = ILL_Hypothesis_proof premise in
         
         (* Return dereliction proof *)
         ILL_Dereliction_proof (ill_seq.context, exp_formula, ill_seq.goal, subproof)
         
     | _ -> raise (ILL_Rule_Application_Exception (true, "Dereliction rule requires !A formula at specified position")))

(* Apply ILL promotion rule: !Γ ⊢ !A / !Γ ⊢ A
   @param rule_req - Rule request
   @param ill_seq - Sequent with form !Γ ⊢ !A
   @return ill_proof - Promotion proof
*)
and apply_promotion_rule _rule_req ill_seq =
    (* Validate ILL constraint: exactly one formula on RHS *)
    validate_single_conclusion ill_seq;
    
    (* Validate that goal is exponential !A *)
    (match ill_seq.goal with
     | Ofcourse inner_formula ->
         (* Validate that all context formulas are exponential *)
         let all_exponential = List.for_all is_ofcourse ill_seq.context in
         if not all_exponential then
             raise (ILL_Rule_Application_Exception (true, "Promotion rule requires all context formulas to be exponential (!)"));
         
         (* Construct premise sequent: !Γ ⊢ A (without ! on goal) *)
         let premise = { context = ill_seq.context; goal = inner_formula } in
         
         (* Validate premise is well-formed *)
         validate_ill_sequent_constraints premise;
         
         (* Create hypothesis proof for premise *)
         let subproof = ILL_Hypothesis_proof premise in
         
         (* Return promotion proof *)
         ILL_Promotion_proof (ill_seq.context, ill_seq.goal, subproof)
         
     | _ -> raise (ILL_Rule_Application_Exception (true, "Promotion rule requires goal !A")))

(* CONTEXT MANAGEMENT *)

(* Helper function to split list at specific position.
   @param list - List to split
   @param pos - Position to split at (0-indexed)
   @return (before, at_pos, after) - Elements before position, element at position, elements after
*)
and split_list_at_position list pos =
    let rec split acc n = function
        | [] -> raise (ILL_Rule_Application_Exception (true, "Position " ^ string_of_int pos ^ " out of bounds"))
        | h :: t when n = 0 -> (List.rev acc, h, t)
        | h :: t -> split (h :: acc) (n - 1) t
    in
    split [] pos list

(* Split context for tensor rule based on user interaction.
   In ILL, tensor rule requires splitting the context between two premises.
   @param context - Original context
   @param split_info - Information about how to split (from user interaction)
   @return (formula list * formula list) - Left and right contexts
*)
let split_context_for_tensor context _split_info =
    (* TODO: Implement intelligent context splitting *)
    (* For now, return simple split *)
    match context with
    | [] -> ([], [])
    | [f] -> ([f], [])
    | f1 :: f2 :: rest -> ([f1], f2 :: rest)

(* MAIN API ENTRY POINT *)

(* Main entry point for ILL rule application API.
   Called by the web server when processing rule application requests.
   @param request_as_json - JSON request from frontend
   @return (bool * Yojson.Basic.t) - (success, response_json)
*)
let apply_rule request_as_json =
    try 
        (* Apply the rule *)
        let ill_proof = apply_rule_with_exceptions request_as_json in
        
        (* Convert to JSON for response *)
        let proof_json = Ill_proof.to_json ill_proof in
        
        (* Return success response *)
        (true, `Assoc [
            ("success", `Bool true);
            ("proof", proof_json)
        ])
    with
    | ILL_Rule_Application_Exception (is_pedagogic, msg) ->
        if is_pedagogic then
            (* User error - return as successful response with error message *)
            (true, `Assoc [
                ("success", `Bool false);
                ("errorMessage", `String msg)
            ])
        else
            (* System error - return as HTTP error *)
            (false, `String ("ILL rule application error: " ^ msg))
    | Failure msg ->
        (* Catch failwith calls *)
        (false, `String ("ILL rule application failure: " ^ msg))
    | exn ->
        (* Catch all other exceptions *)
        (false, `String ("Unexpected error in ILL rule application: " ^ (Printexc.to_string exn)))

(* PROOF VALIDATION HELPERS *)

(* Validate that a proof tree is well-formed after rule application.
   @param proof - ILL proof tree to validate
   @return bool - True if proof is valid
*)
let validate_proof_structure _proof =
    (* TODO: Implement structural validation *)
    (* Check that:
       - All premises match rule requirements
       - Sequents are well-formed
       - No circular dependencies
    *)
    true

(* Check if a rule application creates the expected premise structure.
   @param rule - Applied rule
   @param original_seq - Original sequent
   @param premises - Generated premise sequents
   @return bool - True if premises are correct
*)
let validate_premises _rule _original_seq _premises =
    (* TODO: Implement premise validation *)
    (* Verify that premises match what the rule should generate *)
    true

(* DEBUGGING AND LOGGING *)

(* Generate debug information for rule application.
   @param rule_req - Applied rule request
   @param ill_seq - Original sequent
   @param result - Resulting proof
   @return string - Debug information
*)
let debug_rule_application rule_req ill_seq _result =
    let rule_name = rule_name rule_req.rule in
    let seq_str = ill_sequent_to_ascii ill_seq in
    Printf.sprintf "Applied ILL rule %s to sequent: %s" rule_name seq_str