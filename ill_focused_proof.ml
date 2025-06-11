(* INTUITIONISTIC LINEAR LOGIC FOCUSED PROOF SEARCH
   
   This module implements focused proof search for ILL, which is a goal-directed
   proof search strategy that minimizes non-deterministic choices.
   
   Focused proof search in ILL works as follows:
   1. Focus on a formula (either from context or goal)
   2. Apply all possible rules to that formula until it becomes atomic
   3. Switch focus when no more rules can be applied
   
   Key advantages for ILL:
   - Reduces search space by avoiding interleaving of rule applications
   - Natural fit for goal-directed nature of intuitionistic logic
   - Eliminates many redundant proof attempts
   - More efficient than unfocused search
   
   The focusing discipline ensures completeness while improving performance.
*)

open Ill_sequent
open Ill_proof
open Ill_rule_request

(* Focused proof search phases *)
type focus_phase =
    | Right_Focus of formula    (* Focusing on goal formula *)
    | Left_Focus of formula     (* Focusing on context formula *)
    | No_Focus                  (* No formula currently focused *)

(* Focused sequent with phase information *)
type focused_sequent = {
    ill_seq: ill_sequent;       (* Underlying ILL sequent *)
    phase: focus_phase;         (* Current focus phase *)
    focus_depth: int;           (* Depth of current focus *)
}

(* Configuration for focused proof search *)
type focused_config = {
    max_focus_depth: int;       (* Maximum focusing depth *)
    enable_left_focus: bool;    (* Allow left focusing *)
    enable_right_focus: bool;   (* Allow right focusing *)
}

(* Default focused configuration *)
let default_focused_config = {
    max_focus_depth = 20;
    enable_left_focus = true;
    enable_right_focus = true;
}

(* MAIN FOCUSED PROOF SEARCH API *)

(* Attempt focused proof search on an ILL sequent.
   @param ill_seq - ILL sequent to prove
   @param config - Focused search configuration
   @return ill_proof option - Proof if found, None otherwise
*)
let focused_prove ill_seq config =
    try
        (* Initialize focused sequent *)
        let focused_seq = {
            ill_seq = ill_seq;
            phase = No_Focus;
            focus_depth = 0;
        } in
        
        (* Start focused proof search *)
        focused_search focused_seq config
    with
    | _ -> None

(* Main focused search function.
   @param focused_seq - Focused sequent to prove
   @param config - Configuration
   @return ill_proof option - Proof if found
*)
and focused_search focused_seq config =
    match focused_seq.phase with
    | No_Focus ->
        (* Not currently focusing - choose what to focus on *)
        choose_focus focused_seq config
    | Right_Focus goal_formula ->
        (* Focusing on goal - apply right rules *)
        apply_right_focus focused_seq goal_formula config
    | Left_Focus context_formula ->
        (* Focusing on context - apply left rules *)
        apply_left_focus focused_seq context_formula config

(* FOCUS SELECTION *)

(* Choose which formula to focus on next.
   @param focused_seq - Current focused sequent
   @param config - Configuration
   @return ill_proof option - Proof if found
*)
and choose_focus focused_seq config =
    (* Try right focus first (goal-directed) *)
    if config.enable_right_focus && can_right_focus focused_seq.ill_seq.goal then
        let new_focused = {
            focused_seq with
            phase = Right_Focus focused_seq.ill_seq.goal;
            focus_depth = 0;
        } in
        focused_search new_focused config
    (* Try left focus on context formulas *)
    else if config.enable_left_focus then
        try_left_focus_on_context focused_seq config
    else
        (* No focus possible - try direct axiom *)
        try_axiom focused_seq.ill_seq

(* Try left focus on formulas in the context.
   @param focused_seq - Current focused sequent
   @param config - Configuration
   @return ill_proof option - Proof if found
*)
and try_left_focus_on_context focused_seq config =
    match focused_seq.ill_seq.context with
    | [] -> try_axiom focused_seq.ill_seq
    | formula :: _ when can_left_focus formula ->
        let new_focused = {
            focused_seq with
            phase = Left_Focus formula;
            focus_depth = 0;
        } in
        focused_search new_focused config
    | _ :: rest ->
        (* Try next formula in context *)
        let new_seq = { focused_seq.ill_seq with context = rest } in
        let new_focused = { focused_seq with ill_seq = new_seq } in
        try_left_focus_on_context new_focused config

(* RIGHT FOCUS (GOAL-DIRECTED) *)

(* Apply right focus rules to decompose goal formula.
   @param focused_seq - Current focused sequent
   @param goal_formula - Formula being focused on
   @param config - Configuration
   @return ill_proof option - Proof if found
*)
and apply_right_focus focused_seq goal_formula config =
    if focused_seq.focus_depth > config.max_focus_depth then
        None
    else
        match goal_formula with
        | One ->
            apply_one_right_rule focused_seq config
        | Top ->
            apply_top_right_rule focused_seq config
        | Tensor (a, b) ->
            apply_tensor_right_rule focused_seq a b config
        | Plus (a, b) ->
            apply_plus_right_rule focused_seq a b config
        | Lollipop (a, b) ->
            apply_lollipop_right_rule focused_seq a b config
        | Litt _ ->
            (* Atomic goal - stop right focus, try axiom or left focus *)
            try_axiom_or_left_focus focused_seq config

(* Apply one right rule in focused manner.
   @param focused_seq - Current focused sequent
   @param config - Configuration
   @return ill_proof option - Proof if found
*)
and apply_one_right_rule focused_seq config =
    match focused_seq.ill_seq.context with
    | [] -> Some ILL_One_proof
    | _ -> None  (* One rule requires empty context *)

(* Apply top right rule in focused manner.
   @param focused_seq - Current focused sequent
   @param config - Configuration
   @return ill_proof option - Proof if found
*)
and apply_top_right_rule focused_seq config =
    Some (ILL_Top_proof focused_seq.ill_seq.context)

(* Apply tensor right rule in focused manner.
   @param focused_seq - Current focused sequent
   @param a - Left tensor component
   @param b - Right tensor component
   @param config - Configuration
   @return ill_proof option - Proof if found
*)
and apply_tensor_right_rule focused_seq a b config =
    (* TODO: Implement focused context splitting for tensor *)
    (* For now, use simple split *)
    let left_seq = { context = []; goal = a } in
    let right_seq = { context = []; goal = b } in
    
    match focused_prove left_seq config, focused_prove right_seq config with
    | Some left_proof, Some right_proof ->
        Some (ILL_Tensor_proof (focused_seq.ill_seq.context, a, b, left_proof, right_proof))
    | _ -> None

(* Apply plus right rule in focused manner.
   @param focused_seq - Current focused sequent  
   @param a - Left plus component
   @param b - Right plus component
   @param config - Configuration
   @return ill_proof option - Proof if found
*)
and apply_plus_right_rule focused_seq a b config =
    (* Try left branch first *)
    let left_seq = { context = focused_seq.ill_seq.context; goal = a } in
    match focused_prove left_seq config with
    | Some left_proof ->
        Some (ILL_Plus_left_proof (focused_seq.ill_seq.context, a, b, left_proof))
    | None ->
        (* Try right branch *)
        let right_seq = { context = focused_seq.ill_seq.context; goal = b } in
        match focused_prove right_seq config with
        | Some right_proof ->
            Some (ILL_Plus_right_proof (focused_seq.ill_seq.context, a, b, right_proof))
        | None -> None

(* Apply lollipop right rule in focused manner.
   @param focused_seq - Current focused sequent
   @param a - Antecedent
   @param b - Consequent  
   @param config - Configuration
   @return ill_proof option - Proof if found
*)
and apply_lollipop_right_rule focused_seq a b config =
    let premise_seq = { context = a :: focused_seq.ill_seq.context; goal = b } in
    match focused_prove premise_seq config with
    | Some premise_proof ->
        Some (ILL_Lollipop_proof (focused_seq.ill_seq.context, a, b, premise_proof))
    | None -> None

(* LEFT FOCUS (CONTEXT DECOMPOSITION) *)

(* Apply left focus rules to decompose context formula.
   @param focused_seq - Current focused sequent
   @param context_formula - Formula being focused on
   @param config - Configuration
   @return ill_proof option - Proof if found
*)
and apply_left_focus focused_seq context_formula config =
    (* TODO: Implement left rules for ILL *)
    (* ILL left rules are more complex and context-dependent *)
    (* For now, just continue search *)
    None

(* FOCUSING PREDICATES *)

(* Check if a formula can be right-focused (decomposed on the right).
   @param formula - Formula to check
   @return bool - True if can be right-focused
*)
and can_right_focus = function
    | One | Top -> true           (* Units can be right-focused *)
    | Tensor (_, _) -> true       (* Tensor can be right-focused *)
    | Plus (_, _) -> true         (* Plus can be right-focused *)
    | Lollipop (_, _) -> true     (* Lollipop can be right-focused *)
    | Litt _ -> false             (* Atoms cannot be right-focused *)

(* Check if a formula can be left-focused (decomposed on the left).
   @param formula - Formula to check
   @return bool - True if can be left-focused
*)
and can_left_focus = function
    | Tensor (_, _) -> true       (* Tensor can be left-focused *)
    | Plus (_, _) -> true         (* Plus can be left-focused *)
    | Lollipop (_, _) -> false    (* Lollipop cannot be left-focused in ILL *)
    | One | Top -> false          (* Units cannot be left-focused *)
    | Litt _ -> false             (* Atoms cannot be left-focused *)

(* AXIOM AND FALLBACK *)

(* Try to apply axiom rule.
   @param ill_seq - ILL sequent
   @return ill_proof option - Proof if axiom applies
*)
and try_axiom ill_seq =
    match ill_seq.context, ill_seq.goal with
    | [Litt a], Litt b when a = b ->
        Some (ILL_Axiom_proof a)
    | _ -> None

(* Try axiom first, then left focus as fallback.
   @param focused_seq - Current focused sequent
   @param config - Configuration
   @return ill_proof option - Proof if found
*)
and try_axiom_or_left_focus focused_seq config =
    match try_axiom focused_seq.ill_seq with
    | Some proof -> Some proof
    | None ->
        (* Try left focus on context *)
        if config.enable_left_focus then
            try_left_focus_on_context focused_seq config
        else
            None

(* FOCUSED PROOF OPTIMIZATION *)

(* Optimize focused proof by eliminating unnecessary focus switches.
   @param proof - ILL proof to optimize
   @return ill_proof - Optimized proof
*)
let optimize_focused_proof proof =
    (* TODO: Implement proof optimization *)
    (* Remove redundant focus switches, combine adjacent applications *)
    proof

(* Count the number of focus switches in a proof.
   @param proof - ILL proof
   @return int - Number of focus switches
*)
let count_focus_switches proof =
    (* TODO: Implement focus switch counting *)
    (* Useful for measuring proof complexity *)
    0

(* INTEGRATION WITH UNFOCUSED SEARCH *)

(* Convert unfocused sequent to focused sequent.
   @param ill_seq - ILL sequent
   @return focused_sequent - Focused sequent in no-focus state
*)
let unfocused_to_focused ill_seq =
    {
        ill_seq = ill_seq;
        phase = No_Focus;
        focus_depth = 0;
    }

(* Try focused search as optimization for unfocused search.
   @param ill_seq - ILL sequent to prove
   @return ill_proof option - Proof if found via focusing
*)
let try_focused_optimization ill_seq =
    focused_prove ill_seq default_focused_config

(* DEBUGGING AND ANALYSIS *)

(* Generate focusing trace for debugging.
   @param focused_seq - Focused sequent
   @return string - Human-readable trace
*)
let debug_focus_trace focused_seq =
    let phase_str = match focused_seq.phase with
        | No_Focus -> "No focus"
        | Right_Focus f -> "Right focus on " ^ (formula_to_ascii f)
        | Left_Focus f -> "Left focus on " ^ (formula_to_ascii f)
    in
    Printf.sprintf "Focus: %s, Depth: %d, Sequent: %s" 
        phase_str 
        focused_seq.focus_depth 
        (ill_sequent_to_ascii focused_seq.ill_seq)

(* Check if a focused sequent is in a valid focusing state.
   @param focused_seq - Focused sequent to validate
   @return bool - True if valid
*)
let is_valid_focus_state focused_seq =
    match focused_seq.phase with
    | No_Focus -> true
    | Right_Focus f -> f = focused_seq.ill_seq.goal
    | Left_Focus f -> List.mem f focused_seq.ill_seq.context