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

(* RULE APPLICATION CORE *)

(* Apply an ILL rule to a sequent with full error handling.
   This is the main entry point for rule application.
   @param request_as_json - JSON request from frontend
   @return ill_proof - New proof tree with rule applied
   @raises ILL_Rule_Application_Exception for invalid applications
*)
let rec apply_rule_with_exceptions request_as_json =
    try
        (* Extract rule request from JSON *)
        let rule_request_json = Request_utils.get_key request_as_json "ruleRequest" in
        let rule_request = from_json rule_request_json in
        
        (* Extract sequent with notations *)
        let _sequent_json = Request_utils.get_key request_as_json "sequent" in
        (* TODO: Parse sequent from JSON properly *)
        let stub_sequent = { context = [Litt "A"]; goal = Litt "A" } in
        
        (* Extract notations (if any) *)
        let notations = [] in  (* TODO: Parse notations *)
        
        (* Apply the rule *)
        apply_ill_rule_internal rule_request stub_sequent notations
        
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
    let can_apply, error_msg = can_apply_rule rule_req.rule ill_seq in
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
    | ILL_Plus_left ->
        apply_plus_left_rule ill_seq
    | ILL_Plus_right ->
        apply_plus_right_rule ill_seq
    | ILL_Lollipop ->
        apply_lollipop_rule ill_seq

(* INDIVIDUAL RULE IMPLEMENTATIONS *)

(* Apply ILL axiom rule: A ⊢ A
   @param ill_seq - Sequent with form [A] ⊢ A
   @return ill_proof - Axiom proof
*)
and apply_axiom_rule ill_seq =
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
    match ill_seq.goal with
    | Tensor (a, b) ->
        (* TODO: Implement proper context splitting *)
        (* For now, create stub premises *)
        let premise1 = { context = []; goal = a } in
        let premise2 = { context = []; goal = b } in
        let subproof1 = ILL_Hypothesis_proof premise1 in
        let subproof2 = ILL_Hypothesis_proof premise2 in
        ILL_Tensor_proof (ill_seq.context, a, b, subproof1, subproof2)
    | _ ->
        raise (ILL_Rule_Application_Exception (true, "Tensor rule requires goal A⊗B"))

(* Apply ILL plus left rule: Γ ⊢ A⊕B becomes Γ ⊢ A
   @param ill_seq - Sequent with goal A⊕B
   @return ill_proof - Plus left proof
*)
and apply_plus_left_rule ill_seq =
    match ill_seq.goal with
    | Plus (a, b) ->
        let premise = { context = ill_seq.context; goal = a } in
        let subproof = ILL_Hypothesis_proof premise in
        ILL_Plus_left_proof (ill_seq.context, a, b, subproof)
    | _ ->
        raise (ILL_Rule_Application_Exception (true, "Plus left rule requires goal A⊕B"))

(* Apply ILL plus right rule: Γ ⊢ A⊕B becomes Γ ⊢ B
   @param ill_seq - Sequent with goal A⊕B
   @return ill_proof - Plus right proof
*)
and apply_plus_right_rule ill_seq =
    match ill_seq.goal with
    | Plus (a, b) ->
        let premise = { context = ill_seq.context; goal = b } in
        let subproof = ILL_Hypothesis_proof premise in
        ILL_Plus_right_proof (ill_seq.context, a, b, subproof)
    | _ ->
        raise (ILL_Rule_Application_Exception (true, "Plus right rule requires goal A⊕B"))

(* Apply ILL lollipop rule: Γ ⊢ A⊸B becomes Γ,A ⊢ B
   @param ill_seq - Sequent with goal A⊸B
   @return ill_proof - Lollipop proof
*)
and apply_lollipop_rule ill_seq =
    match ill_seq.goal with
    | Lollipop (a, b) ->
        let premise = { context = a :: ill_seq.context; goal = b } in
        let subproof = ILL_Hypothesis_proof premise in
        ILL_Lollipop_proof (ill_seq.context, a, b, subproof)
    | _ ->
        raise (ILL_Rule_Application_Exception (true, "Lollipop rule requires goal A⊸B"))

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