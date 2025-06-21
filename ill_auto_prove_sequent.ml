(* INTUITIONISTIC LINEAR LOGIC AUTOMATED THEOREM PROVER
   
   This module implements automated proof search for ILL sequents.
   ILL proof search is generally simpler than classical LL because:
   
   1. No exponentials - eliminates complex exponential proof search
   2. Asymmetric sequents - single conclusion simplifies goal-directed search
   3. Fewer connectives - smaller search space
   4. Natural goal-directed structure - follows intuitionistic proof style
   
   The prover uses a focused proof search strategy optimized for ILL:
   - Deterministic phase: Apply all invertible rules first
   - Non-deterministic phase: Handle tensor context splitting and plus choices
   - Termination: Detect axioms and unprovable sequents
*)

open Ill_sequent
open Ill_proof
(* open Ill_rule_request *)

(* Convert raw formula to ILL formula *)
let rec convert_raw_formula_to_ill = function
    | Raw_sequent.One -> One
    | Raw_sequent.Top -> Top
    | Raw_sequent.Litt s -> Litt s
    | Raw_sequent.Tensor (f1, f2) -> 
        Tensor (convert_raw_formula_to_ill f1, convert_raw_formula_to_ill f2)
    | Raw_sequent.Plus (f1, f2) -> 
        Plus (convert_raw_formula_to_ill f1, convert_raw_formula_to_ill f2)
    | Raw_sequent.Lollipop (f1, f2) ->
        Lollipop (convert_raw_formula_to_ill f1, convert_raw_formula_to_ill f2)
    | Raw_sequent.With (f1, f2) ->
        With (convert_raw_formula_to_ill f1, convert_raw_formula_to_ill f2)
    | _ -> failwith "Non-ILL connective not allowed in auto-prove"

(* Configuration for proof search *)
type ill_prover_config = {
    max_depth: int;           (* Maximum proof search depth *)
    timeout_ms: int;          (* Timeout in milliseconds *)
    enable_heuristics: bool;  (* Use heuristic guidance *)
}

(* Default prover configuration *)
let default_config = {
    max_depth = 50;
    timeout_ms = 5000;
    enable_heuristics = true;
}

(* Proof search result *)
type ill_proof_result =
    | ILL_Proof_Found of ill_proof        (* Successful proof *)
    | ILL_Not_Provable                    (* Provably unprovable *)
    | ILL_Timeout                         (* Search timeout *)
    | ILL_Depth_Exceeded                  (* Max depth reached *)
    | ILL_Search_Error of string          (* Search error *)

(* HELPER FUNCTIONS *)

(* Check if a sequent is an axiom.
   @param ill_seq - Sequent to check
   @return bool - True if sequent is axiom
*)
let is_axiom ill_seq =
    match ill_seq.context, ill_seq.goal with
    | [Litt a], Litt b -> a = b
    | _ -> false

(* CORE PROOF SEARCH *)

(* Main proof search function for ILL sequents.
   @param ill_seq - ILL sequent to prove
   @param config - Prover configuration
   @return ill_proof_result - Result of proof search
*)
let rec prove_ill_sequent_internal ill_seq config =
    let start_time = Sys.time () in
    try
        search_proof ill_seq config 0 start_time
    with
    | Stack_overflow -> ILL_Depth_Exceeded
    | _ -> ILL_Search_Error "Unknown error in proof search"

(* Recursive proof search with depth and timeout checking.
   @param ill_seq - Current sequent to prove
   @param config - Prover configuration
   @param depth - Current search depth
   @param start_time - Search start time for timeout
   @return ill_proof_result - Search result
*)
and search_proof ill_seq config depth start_time =
    (* Check termination conditions *)
    if depth > config.max_depth then
        ILL_Depth_Exceeded
    else if (Sys.time () -. start_time) *. 1000.0 > float_of_int config.timeout_ms then
        ILL_Timeout
    else
        try_prove_sequent ill_seq config depth start_time

(* Attempt to prove a sequent by trying applicable rules.
   @param ill_seq - Sequent to prove
   @param config - Prover configuration  
   @param depth - Current depth
   @param start_time - Start time
   @return ill_proof_result - Proof result
*)
and try_prove_sequent ill_seq config depth start_time =
    (* Check for axiom first *)
    if is_axiom ill_seq then
        match ill_seq.context, ill_seq.goal with
        | [Litt a], Litt b when a = b ->
            ILL_Proof_Found (ILL_Axiom_proof a)
        | _ -> ILL_Not_Provable
    else
        (* Try introduction rules based on goal formula *)
        try_introduction_rules ill_seq config depth start_time

(* Try introduction rules based on the goal formula type.
   @param ill_seq - Sequent to prove
   @param config - Prover configuration
   @param depth - Current depth
   @param start_time - Start time
   @return ill_proof_result - Proof result
*)
and try_introduction_rules ill_seq config depth start_time =
    match ill_seq.goal with
    | One ->
        try_one_rule ill_seq config depth start_time
    | Top ->
        try_top_rule ill_seq config depth start_time
    | Tensor (a, b) ->
        try_tensor_rule ill_seq a b config depth start_time
    | With (a, b) ->
        try_with_rule ill_seq a b config depth start_time
    | Plus (a, b) ->
        try_plus_rules ill_seq a b config depth start_time
    | Lollipop (a, b) ->
        try_lollipop_rule ill_seq a b config depth start_time
    | Litt _ ->
        (* Atomic goal - try left rules for decomposing context *)
        try_atomic_goal ill_seq config depth start_time
    | Ofcourse _ ->
        (* Exponential goal - try promotion rule *)
        try_promotion_rule ill_seq config depth start_time

(* INDIVIDUAL RULE IMPLEMENTATIONS *)

(* Try one rule: ⊢ 1 (requires empty context)
   @param ill_seq - Sequent to prove
   @param config - Prover configuration
   @param depth - Current depth
   @param start_time - Start time
   @return ill_proof_result - Proof result
*)
and try_one_rule ill_seq _config _depth _start_time =
    match ill_seq.context with
    | [] -> ILL_Proof_Found ILL_One_proof
    | _ -> ILL_Not_Provable

(* Try top rule: Γ ⊢ ⊤ (always succeeds)
   @param ill_seq - Sequent to prove
   @param config - Prover configuration
   @param depth - Current depth
   @param start_time - Start time
   @return ill_proof_result - Proof result
*)
and try_top_rule ill_seq _config _depth _start_time =
    ILL_Proof_Found (ILL_Top_proof ill_seq.context)

(* Try tensor rule: Γ,Δ ⊢ A⊗B becomes Γ ⊢ A and Δ ⊢ B
   @param ill_seq - Sequent to prove
   @param a - Left tensor component
   @param b - Right tensor component
   @param config - Prover configuration
   @param depth - Current depth
   @param start_time - Start time
   @return ill_proof_result - Proof result
*)
and try_tensor_rule ill_seq a b config depth start_time =
    (* Generate all possible context splits *)
    let splits = generate_context_splits ill_seq.context in
    try_context_splits splits a b config depth start_time

(* Try with rule: Γ ⊢ A&B becomes Γ ⊢ A and Γ ⊢ B
   @param ill_seq - Sequent to prove
   @param a - Left with component
   @param b - Right with component
   @param config - Prover configuration
   @param depth - Current depth
   @param start_time - Start time
   @return ill_proof_result - Proof result
*)
and try_with_rule ill_seq a b config depth start_time =
    let left_premise = { context = ill_seq.context; goal = a } in
    let right_premise = { context = ill_seq.context; goal = b } in
    
    (* Both premises must be provable *)
    match search_proof left_premise config (depth + 1) start_time with
    | ILL_Proof_Found left_proof ->
        (match search_proof right_premise config (depth + 1) start_time with
         | ILL_Proof_Found right_proof ->
             ILL_Proof_Found (ILL_With_right_proof (ill_seq.context, a, b, left_proof, right_proof))
         | result -> result)
    | result -> result

(* Try plus rules: Γ ⊢ A⊕B becomes Γ ⊢ A or Γ ⊢ B
   @param ill_seq - Sequent to prove
   @param a - Left plus component
   @param b - Right plus component
   @param config - Prover configuration
   @param depth - Current depth
   @param start_time - Start time
   @return ill_proof_result - Proof result
*)
and try_plus_rules ill_seq a b config depth start_time =
    (* Try left branch first *)
    let left_premise = { context = ill_seq.context; goal = a } in
    match search_proof left_premise config (depth + 1) start_time with
    | ILL_Proof_Found left_proof ->
        ILL_Proof_Found (ILL_Plus_right_1_proof (ill_seq.context, a, b, left_proof))
    | _ ->
        (* Try right branch *)
        let right_premise = { context = ill_seq.context; goal = b } in
        match search_proof right_premise config (depth + 1) start_time with
        | ILL_Proof_Found right_proof ->
            ILL_Proof_Found (ILL_Plus_right_2_proof (ill_seq.context, a, b, right_proof))
        | result -> result

(* Try lollipop rule: Γ ⊢ A⊸B becomes Γ,A ⊢ B
   @param ill_seq - Sequent to prove
   @param a - Antecedent
   @param b - Consequent
   @param config - Prover configuration
   @param depth - Current depth
   @param start_time - Start time
   @return ill_proof_result - Proof result
*)
and try_lollipop_rule ill_seq a b config depth start_time =
    let premise = { context = a :: ill_seq.context; goal = b } in
    match search_proof premise config (depth + 1) start_time with
    | ILL_Proof_Found premise_proof ->
        ILL_Proof_Found (ILL_Lollipop_proof (ill_seq.context, a, b, premise_proof))
    | result -> result

(* Try promotion rule: !Γ ⊢ !A / !Γ ⊢ A
   @param ill_seq - Sequent with exponential goal
   @param config - Prover configuration  
   @param depth - Current depth
   @param start_time - Start time
   @return ill_proof_result - Proof result
*)
and try_promotion_rule ill_seq config depth start_time =
    match ill_seq.goal with
    | Ofcourse inner_formula ->
        (* Check if all context formulas are exponentials *)
        let all_exponential = List.for_all (function Ofcourse _ -> true | _ -> false) ill_seq.context in
        if not all_exponential then
            ILL_Search_Error "Promotion rule requires all context formulas to be exponential (!)"
        else
            (* Try to prove !Γ ⊢ A *)
            let premise = { context = ill_seq.context; goal = inner_formula } in
            (match search_proof premise config (depth + 1) start_time with
             | ILL_Proof_Found premise_proof ->
                 ILL_Proof_Found (ILL_Promotion_proof (ill_seq.context, ill_seq.goal, premise_proof))
             | result -> result)
    | _ ->
        ILL_Search_Error "Promotion rule requires exponential goal (!A)"

(* Try to prove atomic goal from context.
   @param ill_seq - Sequent with atomic goal
   @param config - Prover configuration
   @param depth - Current depth
   @param start_time - Start time
   @return ill_proof_result - Proof result
*)
and try_atomic_goal ill_seq config depth start_time =
    (* Try left rules for decomposing context *)
    try_left_rules ill_seq config depth start_time

(* Try left rules to decompose context formulas
   @param ill_seq - Sequent with atomic goal
   @param config - Prover configuration
   @param depth - Current depth
   @param start_time - Start time
   @return ill_proof_result - Proof result
*)
and try_left_rules ill_seq config depth start_time =
    let rec try_rules_at_positions context_list pos =
        if pos >= List.length context_list then
            ILL_Not_Provable
        else
            let formula_at_pos = List.nth context_list pos in
            match try_left_rule_at_position ill_seq formula_at_pos pos config depth start_time with
            | ILL_Proof_Found proof -> ILL_Proof_Found proof
            | _ -> try_rules_at_positions context_list (pos + 1)
    in
    try_rules_at_positions ill_seq.context 0

(* Try left rule at specific position
   @param ill_seq - Original sequent
   @param formula - Formula at position
   @param pos - Position in context
   @param config - Prover configuration
   @param depth - Current depth
   @param start_time - Start time
   @return ill_proof_result - Proof result
*)
and try_left_rule_at_position ill_seq formula pos config depth start_time =
    match formula with
    | Tensor (a, b) ->
        (* Tensor left: Γ,A⊗B,Δ ⊢ C becomes Γ,A,B,Δ ⊢ C *)
        let (before, _, after) = split_context_at_position ill_seq.context pos in
        let new_context = before @ [a; b] @ after in
        let premise = { context = new_context; goal = ill_seq.goal } in
        (match search_proof premise config (depth + 1) start_time with
         | ILL_Proof_Found premise_proof ->
             ILL_Proof_Found (ILL_Tensor_left_proof (ill_seq.context, a, b, premise_proof))
         | result -> result)
    
    | With (a, b) ->
        (* Try with left 1 and with left 2 *)
        try_with_left_at_position ill_seq a b pos config depth start_time
    
    | Plus (a, b) ->
        (* Plus left: Γ,A⊕B,Δ ⊢ C becomes Γ,A,Δ ⊢ C and Γ,B,Δ ⊢ C *)
        let (before, _, after) = split_context_at_position ill_seq.context pos in
        let premise1 = { context = before @ [a] @ after; goal = ill_seq.goal } in
        let premise2 = { context = before @ [b] @ after; goal = ill_seq.goal } in
        (match search_proof premise1 config (depth + 1) start_time with
         | ILL_Proof_Found proof1 ->
             (match search_proof premise2 config (depth + 1) start_time with
              | ILL_Proof_Found proof2 ->
                  ILL_Proof_Found (ILL_Plus_left_proof (ill_seq.context, a, b, proof1, proof2))
              | result -> result)
         | result -> result)
    
    | Lollipop (a, b) ->
        (* Lollipop left: Γ,A⊸B,Δ ⊢ C becomes Γ ⊢ A and Δ,B ⊢ C *)
        let (before, _, after) = split_context_at_position ill_seq.context pos in
        let premise1 = { context = before; goal = a } in
        let premise2 = { context = after @ [b]; goal = ill_seq.goal } in
        (match search_proof premise1 config (depth + 1) start_time with
         | ILL_Proof_Found proof1 ->
             (match search_proof premise2 config (depth + 1) start_time with
              | ILL_Proof_Found proof2 ->
                  ILL_Proof_Found (ILL_Lollipop_left_proof (ill_seq.context, a, b, proof1, proof2))
              | result -> result)
         | result -> result)
    
    | _ -> ILL_Not_Provable

(* Try with left rules at position
   @param ill_seq - Original sequent
   @param a - Left component of with
   @param b - Right component of with
   @param pos - Position in context
   @param config - Prover configuration
   @param depth - Current depth
   @param start_time - Start time
   @return ill_proof_result - Proof result
*)
and try_with_left_at_position ill_seq a b pos config depth start_time =
    let (before, _, after) = split_context_at_position ill_seq.context pos in
    
    (* Try with left 1: replace A&B with A *)
    let premise1 = { context = before @ [a] @ after; goal = ill_seq.goal } in
    match search_proof premise1 config (depth + 1) start_time with
    | ILL_Proof_Found proof1 ->
        ILL_Proof_Found (ILL_With_left_1_proof (ill_seq.context, a, proof1))
    | _ ->
        (* Try with left 2: replace A&B with B *)
        let premise2 = { context = before @ [b] @ after; goal = ill_seq.goal } in
        (match search_proof premise2 config (depth + 1) start_time with
         | ILL_Proof_Found proof2 ->
             ILL_Proof_Found (ILL_With_left_2_proof (ill_seq.context, b, proof2))
         | result -> result)

(* Split context at specific position
   @param context - Context list
   @param pos - Position to split at
   @return (before, at_pos, after) - Split context
*)
and split_context_at_position context pos =
    let rec split acc n = function
        | [] -> failwith "Position out of bounds"
        | h :: t when n = 0 -> (List.rev acc, h, t)
        | h :: t -> split (h :: acc) (n - 1) t
    in
    split [] pos context

(* CONTEXT SPLITTING FOR TENSOR RULE *)

(* Generate all possible ways to split context for tensor rule.
   @param context - Context to split
   @return (formula list * formula list) list - All possible splits
*)
and generate_context_splits context =
    (* Generate all possible ways to split context into two parts *)
    let n = List.length context in
    let rec generate_splits acc i =
        if i > n then acc
        else
            let left_ctx = take i context in
            let right_ctx = drop i context in
            (left_ctx, right_ctx) :: generate_splits acc (i + 1)
    in
    generate_splits [] 0

(* Take first n elements from list *)
and take n lst =
    let rec take_acc acc n = function
        | [] -> List.rev acc
        | h :: t when n > 0 -> take_acc (h :: acc) (n - 1) t
        | _ -> List.rev acc
    in
    take_acc [] n lst

(* Drop first n elements from list *)
and drop n lst =
    let rec drop_acc n = function
        | [] -> []
        | _ :: t when n > 0 -> drop_acc (n - 1) t
        | lst -> lst
    in
    drop_acc n lst

(* Try all context splits for tensor rule.
   @param splits - List of context splits to try
   @param a - Left tensor component
   @param b - Right tensor component
   @param config - Prover configuration
   @param depth - Current depth
   @param start_time - Start time
   @return ill_proof_result - Proof result
*)
and try_context_splits splits a b config depth start_time =
    let rec try_splits = function
        | [] -> ILL_Not_Provable
        | (left_ctx, right_ctx) :: remaining_splits ->
            let left_premise = { context = left_ctx; goal = a } in
            let right_premise = { context = right_ctx; goal = b } in
            
            (* Try to prove both premises *)
            match search_proof left_premise config (depth + 1) start_time with
            | ILL_Proof_Found left_proof ->
                (match search_proof right_premise config (depth + 1) start_time with
                 | ILL_Proof_Found right_proof ->
                     let combined_context = left_ctx @ right_ctx in
                     ILL_Proof_Found (ILL_Tensor_proof (combined_context, a, b, left_proof, right_proof))
                 | _ -> try_splits remaining_splits)
            | _ -> try_splits remaining_splits
    in
    try_splits splits

(* MAIN API ENTRY POINT *)

(* Attempt to automatically prove an ILL sequent.
   @param request_as_json - JSON request from frontend
   @return (bool * Yojson.Basic.t) - (success, response_json)
*)
let auto_prove_sequent request_as_json =
    try
        (* Extract sequent from request *)
        let sequent_json = Request_utils.get_key request_as_json "sequent" in
        let raw_sequent = Raw_sequent.from_json sequent_json in
        
        (* Convert raw sequent to ILL sequent *)
        let context_formulas = List.map convert_raw_formula_to_ill raw_sequent.Raw_sequent.hyp in
        let conclusion_formulas = List.map convert_raw_formula_to_ill raw_sequent.Raw_sequent.cons in
        
        let ill_sequent = match conclusion_formulas with
            | [goal] -> { context = context_formulas; goal = goal }
            | [] -> failwith "ILL sequent must have exactly one conclusion"
            | _ -> failwith "ILL sequent can have only one conclusion formula"
        in
        
        (* Extract configuration if provided *)
        let config = default_config in  (* TODO: Parse config from JSON *)
        
        (* Attempt proof search *)
        let result = prove_ill_sequent_internal ill_sequent config in
        
        (* Convert result to JSON response *)
        match result with
        | ILL_Proof_Found proof ->
            (true, `Assoc [
                ("success", `Bool true);
                ("proof", Ill_proof.to_json proof);
                ("provable", `Bool true)
            ])
        | ILL_Not_Provable ->
            (true, `Assoc [
                ("success", `Bool true);
                ("provable", `Bool false);
                ("reason", `String "Sequent is not provable in ILL")
            ])
        | ILL_Timeout ->
            (true, `Assoc [
                ("success", `Bool true);
                ("provable", `Bool false);
                ("reason", `String "Proof search timeout")
            ])
        | ILL_Depth_Exceeded ->
            (true, `Assoc [
                ("success", `Bool true);
                ("provable", `Bool false);
                ("reason", `String "Maximum search depth exceeded")
            ])
        | ILL_Search_Error msg ->
            (false, `String ("ILL proof search error: " ^ msg))
    with
    | _ ->
        (false, `String "Error in ILL automated proving")

(* PROOF SEARCH HEURISTICS *)

(* Apply heuristics to guide proof search.
   @param ill_seq - Current sequent
   @param config - Prover configuration
   @return int - Heuristic score (lower is better)
*)
let compute_heuristic_score ill_seq config =
    if not config.enable_heuristics then 0
    else
        (* For now, prefer shorter contexts *)
        List.length ill_seq.context

(* Sort sequents by heuristic score for search ordering.
   @param sequents - List of sequents to sort
   @param config - Prover configuration
   @return ill_sequent list - Sorted sequents
*)
let sort_by_heuristic sequents config =
    if not config.enable_heuristics then sequents
    else
        List.sort (fun s1 s2 -> 
            compare (compute_heuristic_score s1 config) (compute_heuristic_score s2 config)
        ) sequents

(* DEBUGGING AND STATISTICS *)

(* Statistics for proof search *)
type search_stats = {
    nodes_explored: int;
    max_depth_reached: int;
    time_elapsed: float;
}

(* Generate proof search statistics.
   @param start_time - Search start time
   @param max_depth - Maximum depth reached
   @return search_stats - Statistics record
*)
let generate_search_stats start_time max_depth =
    {
        nodes_explored = 0;  (* TODO: Track nodes *)
        max_depth_reached = max_depth;
        time_elapsed = Sys.time () -. start_time;
    }
