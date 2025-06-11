(* INTUITIONISTIC LINEAR LOGIC AUTO-REVERSE MODULE
   
   This module automatically applies reversible (invertible) rules in ILL.
   Reversible rules are those where applying the rule does not lose information
   and there is essentially only one way to apply them.
   
   In ILL, the reversible rules are:
   - Top introduction: Γ ⊢ ⊤ (always applicable)
   - Lollipop introduction: Γ ⊢ A⊸B → Γ,A ⊢ B (deterministic)
   
   Non-reversible rules that require user choice:
   - Tensor introduction: requires context splitting choice
   - Plus introduction: requires left/right choice
   - Axiom: only applicable in specific cases
   
   This module helps users by automatically applying obvious rules,
   reducing the number of manual clicks needed for proof construction.
*)

open Ill_sequent
open Ill_proof
open Ill_rule_request

(* Configuration for auto-reverse behavior *)
type auto_reverse_config = {
    enable_top_auto: bool;        (* Auto-apply top rules *)
    enable_lollipop_auto: bool;   (* Auto-apply lollipop rules *)
    max_auto_depth: int;          (* Maximum auto-application depth *)
}

(* Default auto-reverse configuration *)
let default_auto_config = {
    enable_top_auto = true;
    enable_lollipop_auto = true;
    max_auto_depth = 10;
}

(* Result of auto-reverse application *)
type auto_reverse_result = {
    modified: bool;               (* Whether any rules were applied *)
    new_proof: ill_proof;         (* Resulting proof tree *)
    rules_applied: string list;   (* List of rules that were applied *)
}

(* CORE AUTO-REVERSE LOGIC *)

(* Apply automatic reversible rules to a proof tree.
   @param proof - ILL proof tree
   @param config - Auto-reverse configuration
   @return auto_reverse_result - Result of auto-reverse
*)
let apply_auto_reverse_internal _proof _config =
    (* TODO: Implement auto-reverse logic *)
    { modified = false; new_proof = ILL_Hypothesis_proof { context = []; goal = Litt "A" }; rules_applied = [] }

(* MAIN API ENTRY POINT *)

(* Apply automatic reversible rules to an ILL sequent.
   @param request_as_json - JSON request from frontend
   @return (bool * Yojson.Basic.t) - (success, response_json)
*)
let auto_reverse_sequent request_as_json =
    try
        (* Extract sequent from request *)
        let _sequent_json = Request_utils.get_key request_as_json "sequent" in
        (* TODO: Parse sequent from JSON properly *)
        let stub_sequent = { context = [Litt "A"]; goal = Litt "A" } in
        
        (* Extract proof from request *)
        let _proof_json = Request_utils.get_key request_as_json "proof" in
        (* TODO: Parse proof from JSON properly *)
        let stub_proof = ILL_Hypothesis_proof stub_sequent in
        
        (* Extract configuration if provided *)
        let config = default_auto_config in  (* TODO: Parse config from JSON *)
        
        (* Apply auto-reverse *)
        let result = apply_auto_reverse_internal stub_proof config in
        
        (* Convert result to JSON response *)
        (true, `Assoc [
            ("success", `Bool true);
            ("modified", `Bool result.modified);
            ("proof", Ill_proof.to_json result.new_proof);
            ("rulesApplied", `List (List.map (fun s -> `String s) result.rules_applied))
        ])
    with
    | _ ->
        (false, `String "Error in ILL auto-reverse")

(* CORE AUTO-REVERSE LOGIC *)

(* Apply automatic reversible rules to a proof tree.
   @param proof - ILL proof tree
   @param config - Auto-reverse configuration
   @return auto_reverse_result - Result of auto-reverse
*)
let rec apply_auto_reverse_internal proof config =
    let rec auto_reverse_recursive current_proof depth rules_applied =
        if depth > config.max_auto_depth then
            { modified = false; new_proof = current_proof; rules_applied = rules_applied }
        else
            match try_auto_reverse_step current_proof config with
            | Some (new_proof, rule_name) ->
                (* Rule was applied, continue recursively *)
                auto_reverse_recursive new_proof (depth + 1) (rule_name :: rules_applied)
            | None ->
                (* No more rules to apply *)
                let was_modified = rules_applied <> [] in
                { modified = was_modified; new_proof = current_proof; rules_applied = List.rev rules_applied }
    in
    auto_reverse_recursive proof 0 []

(* Try to apply one auto-reverse step to a proof.
   @param proof - Current proof tree
   @param config - Configuration
   @return (ill_proof * string) option - New proof and rule name if applied
*)
and try_auto_reverse_step proof config =
    match proof with
    | ILL_Hypothesis_proof ill_seq ->
        (* Try to apply auto-reverse to hypothesis *)
        try_auto_reverse_hypothesis ill_seq config
    | _ ->
        (* Try to apply auto-reverse to subproofs *)
        try_auto_reverse_subproofs proof config

(* HYPOTHESIS AUTO-REVERSE *)

(* Try to apply auto-reverse rules to a hypothesis sequent.
   @param ill_seq - ILL sequent
   @param config - Configuration
   @return (ill_proof * string) option - New proof and rule name if applied
*)
and try_auto_reverse_hypothesis ill_seq config =
    (* Try rules in order of preference *)
    match try_auto_top_rule ill_seq config with
    | Some result -> Some result
    | None ->
        match try_auto_lollipop_rule ill_seq config with
        | Some result -> Some result
        | None -> None

(* Try to automatically apply top rule.
   @param ill_seq - ILL sequent
   @param config - Configuration
   @return (ill_proof * string) option - New proof and rule name if applied
*)
and try_auto_top_rule ill_seq config =
    if config.enable_top_auto then
        match ill_seq.goal with
        | Top ->
            let top_proof = ILL_Top_proof ill_seq.context in
            Some (top_proof, "top")
        | _ -> None
    else
        None

(* Try to automatically apply lollipop rule.
   @param ill_seq - ILL sequent
   @param config - Configuration
   @return (ill_proof * string) option - New proof and rule name if applied
*)
and try_auto_lollipop_rule ill_seq config =
    if config.enable_lollipop_auto then
        match ill_seq.goal with
        | Lollipop (a, b) ->
            let premise_seq = { context = a :: ill_seq.context; goal = b } in
            let premise_proof = ILL_Hypothesis_proof premise_seq in
            let lollipop_proof = ILL_Lollipop_proof (ill_seq.context, a, b, premise_proof) in
            Some (lollipop_proof, "lollipop")
        | _ -> None
    else
        None

(* SUBPROOF AUTO-REVERSE *)

(* Try to apply auto-reverse to subproofs of a proof tree.
   @param proof - Proof tree with subproofs
   @param config - Configuration
   @return (ill_proof * string) option - New proof and rule name if applied
*)
and try_auto_reverse_subproofs proof config =
    match proof with
    | ILL_Tensor_proof (ctx, a, b, p1, p2) ->
        (* Try auto-reverse on left subproof *)
        (match try_auto_reverse_step p1 config with
         | Some (new_p1, rule_name) ->
             let new_proof = ILL_Tensor_proof (ctx, a, b, new_p1, p2) in
             Some (new_proof, rule_name)
         | None ->
             (* Try auto-reverse on right subproof *)
             (match try_auto_reverse_step p2 config with
              | Some (new_p2, rule_name) ->
                  let new_proof = ILL_Tensor_proof (ctx, a, b, p1, new_p2) in
                  Some (new_proof, rule_name)
              | None -> None))
    
    | ILL_Plus_left_proof (ctx, a, b, p) ->
        (* Try auto-reverse on subproof *)
        (match try_auto_reverse_step p config with
         | Some (new_p, rule_name) ->
             let new_proof = ILL_Plus_left_proof (ctx, a, b, new_p) in
             Some (new_proof, rule_name)
         | None -> None)
    
    | ILL_Plus_right_proof (ctx, a, b, p) ->
        (* Try auto-reverse on subproof *)
        (match try_auto_reverse_step p config with
         | Some (new_p, rule_name) ->
             let new_proof = ILL_Plus_right_proof (ctx, a, b, new_p) in
             Some (new_proof, rule_name)
         | None -> None)
    
    | ILL_Lollipop_proof (ctx, a, b, p) ->
        (* Try auto-reverse on subproof *)
        (match try_auto_reverse_step p config with
         | Some (new_p, rule_name) ->
             let new_proof = ILL_Lollipop_proof (ctx, a, b, new_p) in
             Some (new_proof, rule_name)
         | None -> None)
    
    | _ ->
        (* No subproofs or cannot auto-reverse *)
        None

(* REVERSIBILITY ANALYSIS *)

(* Check if a rule is reversible (invertible) in ILL.
   @param rule - ILL rule to check
   @return bool - True if rule is reversible
*)
let is_reversible_rule = function
    | ILL_Top -> true           (* Top is always reversible *)
    | ILL_Lollipop -> true      (* Lollipop is reversible *)
    | ILL_Tensor_left -> true   (* Tensor left is reversible *)
    | ILL_Lollipop_left -> true (* Lollipop left is reversible *)
    | ILL_Axiom -> false        (* Axiom requires specific conditions *)
    | ILL_One -> false          (* One requires empty context *)
    | ILL_Tensor -> false       (* Tensor requires context split choice *)
    | ILL_Plus_left -> false    (* Plus requires left/right choice *)
    | ILL_Plus_right -> false   (* Plus requires left/right choice *)

(* Check if a sequent has a unique reversible rule that applies.
   @param ill_seq - ILL sequent
   @return ill_rule option - Unique reversible rule if exists
*)
let get_unique_reversible_rule ill_seq =
    match ill_seq.goal with
    | Top -> Some ILL_Top
    | Lollipop (_, _) -> Some ILL_Lollipop
    | _ -> None

(* Count the number of reversible rules that could be applied.
   @param ill_seq - ILL sequent
   @return int - Number of applicable reversible rules
*)
let count_applicable_reversible_rules ill_seq =
    let count = ref 0 in
    
    (* Check top rule *)
    (match ill_seq.goal with
     | Top -> incr count
     | _ -> ());
    
    (* Check lollipop rule *)
    (match ill_seq.goal with
     | Lollipop (_, _) -> incr count
     | _ -> ());
    
    !count

(* AUTO-REVERSE STRATEGIES *)

(* Strategy: Apply all reversible rules exhaustively.
   @param proof - ILL proof tree
   @param config - Configuration
   @return auto_reverse_result - Result of exhaustive application
*)
let exhaustive_auto_reverse proof config =
    apply_auto_reverse_internal proof config

(* Strategy: Apply only top-level reversible rules.
   @param proof - ILL proof tree
   @param config - Configuration
   @return auto_reverse_result - Result of top-level application
*)
let top_level_auto_reverse proof config =
    match try_auto_reverse_step proof config with
    | Some (new_proof, rule_name) ->
        { modified = true; new_proof = new_proof; rules_applied = [rule_name] }
    | None ->
        { modified = false; new_proof = proof; rules_applied = [] }

(* Strategy: Apply reversible rules with user confirmation.
   @param proof - ILL proof tree
   @param config - Configuration
   @return auto_reverse_result - Result with confirmation points
*)
let confirmed_auto_reverse proof config =
    (* TODO: Implement confirmation strategy *)
    (* Would require frontend integration for user prompts *)
    apply_auto_reverse_internal proof config

(* UTILITIES *)

(* Create auto-reverse configuration from JSON.
   @param json - JSON configuration
   @return auto_reverse_config - Parsed configuration
*)
let config_from_json _json =
    (* TODO: Implement JSON parsing for auto-reverse config *)
    default_auto_config

(* Convert auto-reverse result to detailed JSON.
   @param result - Auto-reverse result
   @return Yojson.Basic.t - Detailed JSON representation
*)
let result_to_detailed_json result =
    `Assoc [
        ("modified", `Bool result.modified);
        ("proof", Ill_proof.to_json result.new_proof);
        ("rulesApplied", `List (List.map (fun s -> `String s) result.rules_applied));
        ("numRulesApplied", `Int (List.length result.rules_applied))
    ]

(* Generate human-readable summary of auto-reverse result.
   @param result - Auto-reverse result
   @return string - Summary text
*)
let summarize_auto_reverse result =
    if result.modified then
        let num_rules = List.length result.rules_applied in
        let rules_str = String.concat ", " result.rules_applied in
        Printf.sprintf "Applied %d reversible rule(s): %s" num_rules rules_str
    else
        "No reversible rules were applicable"

(* DEBUGGING *)

(* Check if auto-reverse created a valid proof.
   @param original_proof - Original proof before auto-reverse
   @param result - Auto-reverse result
   @return bool - True if result is valid
*)
let validate_auto_reverse_result _original_proof _result =
    (* TODO: Implement validation *)
    (* Check that:
       - Original sequent is preserved
       - Only reversible rules were applied
       - Proof structure is valid
    *)
    true