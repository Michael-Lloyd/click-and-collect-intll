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
    | Raw_sequent.With (_, _) -> 
        raise (ILL_Rule_Application_Exception (true, "& (with) is not allowed in ILL"))
    | Raw_sequent.Ofcourse _ -> 
        raise (ILL_Rule_Application_Exception (true, "! (of course) is not allowed in ILL"))
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
        | Tensor (f1, f2) | Plus (f1, f2) | Lollipop (f1, f2) ->
            validate_formula f1;
            validate_formula f2
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
        
        (* Apply the rule *)
        apply_ill_rule_internal rule_request ill_sequent notations
        
    with
    | Request_utils.Bad_request_exception msg -> 
        raise (ILL_Rule_Application_Exception (false, "Bad request: " ^ msg))
    | ILL_Rule_Json_Exception msg -> 
        raise (ILL_Rule_Application_Exception (false, "Invalid rule JSON: " ^ msg))
    | _ -> 
        raise (ILL_Rule_Application_Exception (false, "Unknown error in rule application"))

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
    | ILL_One ->
        apply_one_rule ill_seq
    | ILL_Top ->
        apply_top_rule ill_seq
    | ILL_Tensor ->
        apply_tensor_rule rule_req ill_seq
    | ILL_Tensor_left ->
        apply_tensor_left_rule ill_seq
    | ILL_Plus_left ->
        apply_plus_left_rule ill_seq
    | ILL_Plus_right ->
        apply_plus_right_rule ill_seq
    | ILL_Lollipop ->
        apply_lollipop_rule ill_seq
    | ILL_Lollipop_left ->
        apply_lollipop_left_rule ill_seq

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

(* Apply ILL one rule: ⊢ 1
   @param ill_seq - Sequent with form [] ⊢ 1
   @return ill_proof - One proof
*)
and apply_one_rule ill_seq =
    (* Validate ILL constraint: exactly one formula on RHS *)
    validate_single_conclusion ill_seq;
    
    match ill_seq.context, ill_seq.goal with
    | [], One ->
        ILL_One_proof
    | _ ->
        raise (ILL_Rule_Application_Exception (true, "One rule requires empty context and goal 1"))

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
and apply_tensor_rule _rule_req ill_seq =
    (* Validate ILL constraint: exactly one formula on RHS *)
    validate_single_conclusion ill_seq;
    
    match ill_seq.goal with
    | Tensor (a, b) ->
        (* Split context between the two premises *)
        let ctx1, ctx2 = Ill_rule_request.split_context_simple ill_seq.context in
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
   @param ill_seq - Sequent with A⊗B in context
   @return ill_proof - Tensor left proof
*)
and apply_tensor_left_rule ill_seq =
    (* Validate ILL constraint: exactly one formula on RHS *)
    validate_single_conclusion ill_seq;
    
    (* Find first tensor in context and expand it *)
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

(* Apply ILL plus left rule: Γ ⊢ A⊕B becomes Γ ⊢ A
   @param ill_seq - Sequent with goal A⊕B
   @return ill_proof - Plus left proof
*)
and apply_plus_left_rule ill_seq =
    (* Validate ILL constraint: exactly one formula on RHS *)
    validate_single_conclusion ill_seq;
    
    match ill_seq.goal with
    | Plus (a, b) ->
        let premise = { context = ill_seq.context; goal = a } in
        
        (* Validate that premise maintains ILL constraints *)
        validate_ill_sequent_constraints premise;
        
        let subproof = ILL_Hypothesis_proof premise in
        ILL_Plus_left_proof (ill_seq.context, a, b, subproof)
    | _ ->
        raise (ILL_Rule_Application_Exception (true, "Plus left rule requires goal A⊕B"))

(* Apply ILL plus right rule: Γ ⊢ A⊕B becomes Γ ⊢ B
   @param ill_seq - Sequent with goal A⊕B
   @return ill_proof - Plus right proof
*)
and apply_plus_right_rule ill_seq =
    (* Validate ILL constraint: exactly one formula on RHS *)
    validate_single_conclusion ill_seq;
    
    match ill_seq.goal with
    | Plus (a, b) ->
        let premise = { context = ill_seq.context; goal = b } in
        
        (* Validate that premise maintains ILL constraints *)
        validate_ill_sequent_constraints premise;
        
        let subproof = ILL_Hypothesis_proof premise in
        ILL_Plus_right_proof (ill_seq.context, a, b, subproof)
    | _ ->
        raise (ILL_Rule_Application_Exception (true, "Plus right rule requires goal A⊕B"))

(* Apply ILL lollipop rule: Γ ⊢ A⊸B becomes Γ,A ⊢ B
   @param ill_seq - Sequent with goal A⊸B
   @return ill_proof - Lollipop proof
*)
and apply_lollipop_rule ill_seq =
    (* Validate ILL constraint: exactly one formula on RHS *)
    validate_single_conclusion ill_seq;
    
    match ill_seq.goal with
    | Lollipop (a, b) ->
        let premise = { context = a :: ill_seq.context; goal = b } in
        
        (* Validate that premise maintains ILL constraints *)
        validate_ill_sequent_constraints premise;
        
        let subproof = ILL_Hypothesis_proof premise in
        ILL_Lollipop_proof (ill_seq.context, a, b, subproof)
    | _ ->
        raise (ILL_Rule_Application_Exception (true, "Lollipop rule requires goal A⊸B"))

(* Apply ILL lollipop left rule: Γ,A⊸B,Δ ⊢ C becomes Γ,Δ ⊢ A and B,Γ,Δ ⊢ C
   @param ill_seq - Sequent with A⊸B in context
   @return ill_proof - Lollipop left proof with two premises
*)
and apply_lollipop_left_rule ill_seq =
    (* Validate ILL constraint: exactly one formula on RHS *)
    validate_single_conclusion ill_seq;
    
    (* Find first lollipop in context and extract it *)
    let rec find_and_extract_lollipop acc = function
        | [] -> raise (ILL_Rule_Application_Exception (true, "Lollipop left rule requires A⊸B in context"))
        | Lollipop (a, b) :: rest ->
            let remaining_context = acc @ rest in
            let premise1 = { context = remaining_context; goal = a } in
            let premise2 = { context = b :: remaining_context; goal = ill_seq.goal } in
            
            (* Validate that both premises maintain ILL constraints *)
            validate_ill_sequent_constraints premise1;
            validate_ill_sequent_constraints premise2;
            
            let subproof1 = ILL_Hypothesis_proof premise1 in
            let subproof2 = ILL_Hypothesis_proof premise2 in
            ILL_Lollipop_left_proof (ill_seq.context, a, b, subproof1, subproof2)
        | f :: rest -> find_and_extract_lollipop (acc @ [f]) rest
    in
    find_and_extract_lollipop [] ill_seq.context

(* CONTEXT MANAGEMENT *)

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
    | _ ->
        (* Unexpected error *)
        (false, `String "Unexpected error in ILL rule application")

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