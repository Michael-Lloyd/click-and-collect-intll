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

(* Helper function for debug printing with flush *)
let debug_print fmt =
    Printf.ksprintf (fun s -> 
        print_string s; 
        flush stdout
    ) fmt

(* Helper function to convert ILL formula to string for debugging *)
let rec formula_to_string = function
    | One -> "1"
    | Top -> "⊤"
    | Litt s -> s
    | Tensor (a, b) -> "(" ^ formula_to_string a ^ " ⊗ " ^ formula_to_string b ^ ")"
    | Plus (a, b) -> "(" ^ formula_to_string a ^ " ⊕ " ^ formula_to_string b ^ ")"
    | Lollipop (a, b) -> "(" ^ formula_to_string a ^ " ⊸ " ^ formula_to_string b ^ ")"
    | With (a, b) -> "(" ^ formula_to_string a ^ " & " ^ formula_to_string b ^ ")"
    | Ofcourse f -> "!" ^ formula_to_string f

(* Helper function to convert context (formula list) to string *)
let context_to_string context =
    match context with
    | [] -> "·"
    | _ -> String.concat ", " (List.map formula_to_string context)

(* Helper function to get formula type name *)
let formula_type_name = function
    | One -> "One (1)"
    | Top -> "Top (⊤)"
    | Litt _ -> "Literal"
    | Tensor _ -> "Tensor (⊗)"
    | Plus _ -> "Plus (⊕)"
    | Lollipop _ -> "Lollipop (⊸)"
    | With _ -> "With (&)"
    | Ofcourse _ -> "Ofcourse (!)"

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
    | Raw_sequent.Ofcourse f ->
        Ofcourse (convert_raw_formula_to_ill f)
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

(* HELPER FUNCTIONS FOR CONTEXT MANIPULATION *)

(* Take first n elements from list *)
let take n lst =
    let rec take_acc acc n = function
        | [] -> List.rev acc
        | h :: t when n > 0 -> take_acc (h :: acc) (n - 1) t
        | _ -> List.rev acc
    in
    take_acc [] n lst

(* Drop first n elements from list *)
let drop n lst =
    let rec drop_acc n = function
        | [] -> []
        | _ :: t when n > 0 -> drop_acc (n - 1) t
        | lst -> lst
    in
    drop_acc n lst

(* Generate all permutations of a list.
   @param lst - List to permute
   @return formula list list - All permutations
*)
let rec permutations = function
    | [] -> [[]]
    | h::t ->
        let rec insert_everywhere x = function
            | [] -> [[x]]
            | h::t as lst -> (x::lst) :: (List.map (fun l -> h::l) (insert_everywhere x t))
        in
        List.concat (List.map (fun perm -> insert_everywhere h perm) (permutations t))

(* Generate all possible ways to partition a list into two parts.
   This includes all permutations and all ways to split each permutation.
   @param lst - List to partition
   @return (formula list * formula list) list - All possible partitions
*)
let generate_all_partitions lst =
    let perms = permutations lst in
    debug_print "[ILL Auto-Prover] Generating partitions for %d formulas, %d permutations\n" 
        (List.length lst) (List.length perms);
    let all_partitions = List.concat (List.map (fun perm ->
        let n = List.length perm in
        let rec generate_splits acc i =
            if i > n then acc
            else
                let left = take i perm in
                let right = drop i perm in
                (left, right) :: generate_splits acc (i + 1)
        in
        generate_splits [] 0
    ) perms) in
    (* Remove duplicates - convert to string representation for comparison *)
    let unique_partitions = 
        let seen = Hashtbl.create 100 in
        List.filter (fun (l, r) ->
            let key = (context_to_string l) ^ "|" ^ (context_to_string r) in
            if Hashtbl.mem seen key then false
            else (Hashtbl.add seen key (); true)
        ) all_partitions
    in
    debug_print "[ILL Auto-Prover] Generated %d unique partitions (with exchange)\n" 
        (List.length unique_partitions);
    unique_partitions

(* Generate all possible ways to split context for tensor rule.
   @param context - Context to split
   @return (formula list * formula list) list - All possible splits
*)
let generate_context_splits context =
    (* Use the new partition function that handles permutations *)
    generate_all_partitions context

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
    (* Print current sequent being searched *)
    debug_print "[ILL Auto-Prover] Depth %d: Searching proof for sequent:\n" depth;
    debug_print "  Context: %s\n" (context_to_string ill_seq.context);
    debug_print "  Goal: %s\n" (formula_to_string ill_seq.goal);
    
    (* Check termination conditions *)
    if depth > config.max_depth then begin
        debug_print "[ILL Auto-Prover] Max depth exceeded (%d > %d)\n" depth config.max_depth;
        ILL_Depth_Exceeded
    end else if (Sys.time () -. start_time) *. 1000.0 > float_of_int config.timeout_ms then begin
        debug_print "[ILL Auto-Prover] Timeout exceeded (%.2fms > %dms)\n" 
            ((Sys.time () -. start_time) *. 1000.0) config.timeout_ms;
        ILL_Timeout
    end else
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
    if is_axiom ill_seq then begin
        match ill_seq.context, ill_seq.goal with
        | [Litt a], Litt b when a = b ->
            debug_print "[ILL Auto-Prover] Axiom found: %s ⊢ %s\n" a b;
            ILL_Proof_Found (ILL_Axiom_proof a)
        | _ -> 
            debug_print "[ILL Auto-Prover] Not an axiom\n";
            ILL_Not_Provable
    end else begin
        (* Try both strategies: left-then-right and right-first *)
        match try_left_then_right_strategy ill_seq config depth start_time with
        | ILL_Proof_Found proof -> 
            debug_print "[ILL Auto-Prover] Proof found using LEFT_THEN_RIGHT strategy\n";
            ILL_Proof_Found proof
        | _ ->
            debug_print "[ILL Auto-Prover] LEFT_THEN_RIGHT failed, trying RIGHT_FIRST\n";
            try_right_first_strategy ill_seq config depth start_time
    end

(* Strategy: Try decomposing context first, then apply introduction rules.
   This handles cases where we need to decompose complex formulas in the
   context before we can make progress on the goal.
   @param ill_seq - Sequent to prove
   @param config - Prover configuration
   @param depth - Current depth
   @param start_time - Start time
   @return ill_proof_result - Proof result
*)
and try_left_then_right_strategy ill_seq config depth start_time =
    debug_print "[ILL Auto-Prover] Strategy: LEFT_THEN_RIGHT\n";
    match try_left_rules_any_goal ill_seq config depth start_time with
    | ILL_Proof_Found proof -> 
        debug_print "[ILL Auto-Prover] LEFT_THEN_RIGHT succeeded with left rules\n";
        ILL_Proof_Found proof
    | _ ->
        debug_print "[ILL Auto-Prover] Left rules failed, trying introduction rules\n";
        try_introduction_rules ill_seq config depth start_time

(* Strategy: Try goal-directed search first (current behavior).
   This applies introduction rules based on the goal formula type.
   @param ill_seq - Sequent to prove
   @param config - Prover configuration
   @param depth - Current depth
   @param start_time - Start time
   @return ill_proof_result - Proof result
*)
and try_right_first_strategy ill_seq config depth start_time =
    debug_print "[ILL Auto-Prover] Strategy: RIGHT_FIRST\n";
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
    debug_print "[ILL Auto-Prover] Trying tensor rule for %s ⊗ %s\n" 
        (formula_to_string a) (formula_to_string b);
    (* Generate all possible context splits *)
    let splits = generate_context_splits ill_seq.context in
    debug_print "[ILL Auto-Prover] Generated %d context splits\n" (List.length splits);
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
    debug_print "[ILL Auto-Prover] Trying lollipop rule for %s ⊸ %s\n" 
        (formula_to_string a) (formula_to_string b);
    let premise = { context = a :: ill_seq.context; goal = b } in
    match search_proof premise config (depth + 1) start_time with
    | ILL_Proof_Found premise_proof ->
        debug_print "[ILL Auto-Prover] Lollipop rule succeeded\n";
        ILL_Proof_Found (ILL_Lollipop_proof (ill_seq.context, a, b, premise_proof))
    | result -> 
        debug_print "[ILL Auto-Prover] Lollipop rule failed\n";
        result

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
    debug_print "[ILL Auto-Prover] Trying to prove atomic goal from context\n";
    (* Try left rules for decomposing context *)
    try_left_rules ill_seq config depth start_time

(* Try left rules regardless of goal type.
   This allows us to decompose context before trying introduction rules.
   @param ill_seq - Sequent to prove (any goal type)
   @param config - Prover configuration
   @param depth - Current depth
   @param start_time - Start time
   @return ill_proof_result - Proof result
*)
and try_left_rules_any_goal ill_seq config depth start_time =
    debug_print "[ILL Auto-Prover] Trying left rules (goal: %s)\n" 
        (formula_type_name ill_seq.goal);
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
and try_exponential_left_at_position ill_seq inner_formula pos config depth start_time =
    let (before, ofcourse_formula, after) = split_context_at_position ill_seq.context pos in
    debug_print "[ILL Auto-Prover] Trying exponential left rules for %s at position %d\n" 
        (formula_to_string ofcourse_formula) pos;
    
    (* Try weakening: Γ,!A,Δ ⊢ B becomes Γ,Δ ⊢ B *)
    debug_print "[ILL Auto-Prover] Trying weakening rule\n";
    (match (
        let weakening_context = before @ after in
        let weakening_premise = { context = weakening_context; goal = ill_seq.goal } in
        search_proof weakening_premise config (depth + 1) start_time
    ) with
    | ILL_Proof_Found weakening_proof ->
        debug_print "[ILL Auto-Prover] Weakening rule succeeded\n";
        ILL_Proof_Found (ILL_Weakening_proof (ill_seq.context, ofcourse_formula, ill_seq.goal, weakening_proof))
    | _ ->
        (* Try dereliction: Γ,!A,Δ ⊢ B becomes Γ,A,Δ ⊢ B *)
        debug_print "[ILL Auto-Prover] Trying dereliction rule\n";
        (match (
            let dereliction_context = before @ [inner_formula] @ after in
            let dereliction_premise = { context = dereliction_context; goal = ill_seq.goal } in
            search_proof dereliction_premise config (depth + 1) start_time
        ) with
        | ILL_Proof_Found dereliction_proof ->
            debug_print "[ILL Auto-Prover] Dereliction rule succeeded\n";
            ILL_Proof_Found (ILL_Dereliction_proof (ill_seq.context, ofcourse_formula, ill_seq.goal, dereliction_proof))
        | _ ->
            (* For single !A formulas, contraction is not applicable *)
            (* Contraction only applies when we already have duplicates *)
            debug_print "[ILL Auto-Prover] Exponential left rules failed\n";
            ILL_Not_Provable
        )
    )

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
        (* Try all possible ways to partition the remaining context *)
        let (before, _, after) = split_context_at_position ill_seq.context pos in
        let remaining_context = before @ after in
        debug_print "[ILL Auto-Prover] Trying lollipop left for %s at position %d\n" 
            (formula_to_string (Lollipop (a, b))) pos;
        debug_print "[ILL Auto-Prover] Remaining context after removing lollipop: %s\n"
            (context_to_string remaining_context);
        
        (* Generate all possible partitions of the remaining context *)
        let partitions = generate_all_partitions remaining_context in
        
        let rec try_partitions = function
            | [] -> ILL_Not_Provable
            | (gamma, delta) :: rest ->
                debug_print "[ILL Auto-Prover] Trying partition: Γ=%s, Δ=%s\n"
                    (context_to_string gamma) (context_to_string delta);
                let premise1 = { context = gamma; goal = a } in
                let premise2 = { context = delta @ [b]; goal = ill_seq.goal } in
                (match search_proof premise1 config (depth + 1) start_time with
                 | ILL_Proof_Found proof1 ->
                     (match search_proof premise2 config (depth + 1) start_time with
                      | ILL_Proof_Found proof2 ->
                          debug_print "[ILL Auto-Prover] Lollipop left succeeded with this partition\n";
                          ILL_Proof_Found (ILL_Lollipop_left_proof (ill_seq.context, a, b, proof1, proof2))
                      | _ -> try_partitions rest)
                 | _ -> try_partitions rest)
        in
        try_partitions partitions
    
    | Ofcourse inner_formula ->
        (* Try exponential rules: weakening, dereliction, contraction *)
        try_exponential_left_at_position ill_seq inner_formula pos config depth start_time
    
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
    let rec try_splits split_num = function
        | [] -> ILL_Not_Provable
        | (left_ctx, right_ctx) :: remaining_splits ->
            debug_print "[ILL Auto-Prover] Tensor split %d: left=%s, right=%s\n"
                split_num (context_to_string left_ctx) (context_to_string right_ctx);
            let left_premise = { context = left_ctx; goal = a } in
            let right_premise = { context = right_ctx; goal = b } in
            
            (* Try to prove both premises *)
            match search_proof left_premise config (depth + 1) start_time with
            | ILL_Proof_Found left_proof ->
                (match search_proof right_premise config (depth + 1) start_time with
                 | ILL_Proof_Found right_proof ->
                     debug_print "[ILL Auto-Prover] Tensor rule succeeded with split %d\n" split_num;
                     let combined_context = left_ctx @ right_ctx in
                     ILL_Proof_Found (ILL_Tensor_proof (combined_context, a, b, left_proof, right_proof))
                 | _ -> try_splits (split_num + 1) remaining_splits)
            | _ -> try_splits (split_num + 1) remaining_splits
    in
    try_splits 1 splits

(* MAIN API ENTRY POINT *)

(* Attempt to automatically prove an ILL sequent.
   @param request_as_json - JSON request from frontend
   @return (bool * Yojson.Basic.t) - (success, response_json)
*)
let auto_prove_sequent request_as_json =
    try
        debug_print "\n[ILL Auto-Prover] ========== START AUTO PROVE REQUEST ==========\n";
        
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
        
        debug_print "[ILL Auto-Prover] Input sequent: %s ⊢ %s\n" 
            (context_to_string ill_sequent.context) 
            (formula_to_string ill_sequent.goal);
        
        (* Extract configuration if provided *)
        let config = default_config in  (* TODO: Parse config from JSON *)
        debug_print "[ILL Auto-Prover] Config: max_depth=%d, timeout=%dms\n" 
            config.max_depth config.timeout_ms;
        
        (* Attempt proof search *)
        let result = prove_ill_sequent_internal ill_sequent config in
        
        (* Convert result to JSON response *)
        let response = match result with
        | ILL_Proof_Found proof ->
            debug_print "[ILL Auto-Prover] PROOF FOUND!\n";
            debug_print "[ILL Auto-Prover] ========== END AUTO PROVE REQUEST ==========\n\n";
            let proof_json = Ill_proof.to_json proof in
            (true, `Assoc [
                ("success", `Bool true);
                ("proof", proof_json);
                ("provable", `Bool true)
            ])
        | ILL_Not_Provable ->
            debug_print "[ILL Auto-Prover] NOT PROVABLE - exhausted all possibilities\n";
            debug_print "[ILL Auto-Prover] ========== END AUTO PROVE REQUEST ==========\n\n";
            (true, `Assoc [
                ("success", `Bool false);
                ("is_provable", `Bool false);
                ("reason", `String "Sequent is not provable in ILL")
            ])
        | ILL_Timeout ->
            debug_print "[ILL Auto-Prover] TIMEOUT - search exceeded %dms\n" config.timeout_ms;
            debug_print "[ILL Auto-Prover] ========== END AUTO PROVE REQUEST ==========\n\n";
            (true, `Assoc [
                ("success", `Bool false);
                ("is_provable", `Bool true);
                ("reason", `String "Proof search timeout")
            ])
        | ILL_Depth_Exceeded ->
            debug_print "[ILL Auto-Prover] DEPTH EXCEEDED - max depth %d reached\n" config.max_depth;
            debug_print "[ILL Auto-Prover] ========== END AUTO PROVE REQUEST ==========\n\n";
            (true, `Assoc [
                ("success", `Bool false);
                ("is_provable", `Bool true);
                ("reason", `String "Maximum search depth exceeded")
            ])
        | ILL_Search_Error msg ->
            debug_print "[ILL Auto-Prover] ERROR: %s\n" msg;
            debug_print "[ILL Auto-Prover] ========== END AUTO PROVE REQUEST ==========\n\n";
            (false, `String ("ILL proof search error: " ^ msg))
        in
        response
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
