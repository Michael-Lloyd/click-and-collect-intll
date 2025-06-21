(* INTUITIONISTIC LINEAR LOGIC RULE REQUEST HANDLING
   
   This module defines the rules available in ILL and handles parsing rule requests
   from the frontend. ILL has a more restricted set of rules compared to classical LL.
   
   Available ILL rules:
   - Axiom: A ⊢ A (identity)
   - One: ⊢ 1 (multiplicative unit introduction)
   - Top: Γ ⊢ ⊤ (additive unit introduction)  
   - Tensor: Γ,Δ ⊢ A⊗B / Γ ⊢ A & Δ ⊢ B (multiplicative conjunction)
   - With_left_1: Γ,A&B ⊢ C / Γ,A ⊢ C (additive conjunction left 1)
   - With_left_2: Γ,A&B ⊢ C / Γ,B ⊢ C (additive conjunction left 2)
   - With_right: Γ ⊢ A&B / Γ ⊢ A & Γ ⊢ B (additive conjunction right)
   - Plus_left: Γ ⊢ A⊕B / Γ ⊢ A (additive disjunction left)
   - Plus_right: Γ ⊢ A⊕B / Γ ⊢ B (additive disjunction right)
   - Lollipop: Γ ⊢ A⊸B / Γ,A ⊢ B (linear implication introduction)
   - Weakening: Γ ⊢ B / Γ,!A ⊢ B (weakening)
   - Contraction: Γ,!A ⊢ B / Γ,!A,!A ⊢ B (contraction)
   - Dereliction: Γ,!A ⊢ B / Γ,A ⊢ B (dereliction)
   - Promotion: !Γ ⊢ !A / !Γ ⊢ A (promotion)
   
   Removed from classical LL:
   - Par rule (no ⅋ connective)
   - With rule has left and right rules
   - Whynot (?) exponential
*)

open Ill_sequent

(* Convert raw formula to ILL formula.
   @param raw_formula - Raw formula from JSON
   @return formula - ILL formula
   @raises ILL_Rule_Json_Exception for non-ILL connectives
*)
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
    (* Invalid connectives for ILL *)
    | Raw_sequent.Bottom -> 
        failwith "⊥ (bottom) is not allowed in ILL"
    | Raw_sequent.Zero -> 
        failwith "0 (zero) is not allowed in ILL"
    | Raw_sequent.Dual _ -> 
        failwith "^ (dual) is not allowed in ILL"
    | Raw_sequent.Par (_, _) -> 
        failwith "⅋ (par) is not allowed in ILL"
    | Raw_sequent.Ofcourse f -> 
        Ofcourse (convert_raw_formula_to_ill f)
    | Raw_sequent.Whynot _ -> 
        failwith "? (why not) is not allowed in ILL"

(* Convert ILL formula to raw formula for JSON serialization.
   @param ill_formula - ILL formula  
   @return Raw_sequent.formula - Raw formula
*)
let rec ill_formula_to_raw = function
    | One -> Raw_sequent.One
    | Top -> Raw_sequent.Top
    | Litt s -> Raw_sequent.Litt s
    | Tensor (f1, f2) -> Raw_sequent.Tensor (ill_formula_to_raw f1, ill_formula_to_raw f2)
    | Plus (f1, f2) -> Raw_sequent.Plus (ill_formula_to_raw f1, ill_formula_to_raw f2)
    | Lollipop (f1, f2) -> Raw_sequent.Lollipop (ill_formula_to_raw f1, ill_formula_to_raw f2)
    | With (f1, f2) -> Raw_sequent.With (ill_formula_to_raw f1, ill_formula_to_raw f2)
    | Ofcourse f -> Raw_sequent.Ofcourse (ill_formula_to_raw f)

(* ILL inference rule types.
   Each rule corresponds to an introduction or elimination rule for the respective connective.
   ILL requires both left (elimination) and right (introduction) rules.
*)
type ill_rule = 
    | ILL_Axiom
    | ILL_One
    | ILL_Top
    | ILL_Tensor
    | ILL_Tensor_left
    | ILL_With_left_1    (* &L₁: left rule for first sub-formula *)
    | ILL_With_left_2    (* &L₂: left rule for second sub-formula *)
    | ILL_With_right     (* &R: right rule *)
    | ILL_Plus_left      (* +L: left rule *)
    | ILL_Plus_right_1   (* +R₁: right rule for left sub-formula *)
    | ILL_Plus_right_2   (* +R₂: right rule for right sub-formula *)
    | ILL_Lollipop
    | ILL_Lollipop_left
    | ILL_Cut            (* Cut: Γ,Δ ⊢ C / Γ ⊢ A & Δ,A ⊢ C *)
    | ILL_Weakening      (* !w: Γ ⊢ B / Γ,!A ⊢ B *)
    | ILL_Contraction    (* !c: Γ,!A ⊢ B / Γ,!A,!A ⊢ B *)
    | ILL_Dereliction    (* !d: Γ,!A ⊢ B / Γ,A ⊢ B *)
    | ILL_Promotion      (* !p: !Γ ⊢ !A / !Γ ⊢ A *)

(* Rule request data structure.
   Contains the rule to apply and additional parameters like formula position.
*)
type ill_rule_request = {
    rule: ill_rule;                    (* Which rule to apply *)
    formula_position: int option;      (* Position of main formula in sequent *)
    side: string option;              (* For rules with choices (left/right) *)
    context_split: int list option;   (* For tensor rule context splitting *)
    sequent_side: string option;     (* Which side of turnstile was clicked (left/right) *)
    cut_formula: formula option;      (* Cut formula for cut rule *)
    cut_position: int option;         (* Position to insert cut in context *)
}

(* Exception for malformed rule requests *)
exception ILL_Rule_Json_Exception of string;;

(* RULE VALIDATION *)

(* Check if a rule can be applied to a given ILL sequent.
   @param rule - The ILL rule to check
   @param ill_seq - The sequent to apply it to
   @return bool * string - (can_apply, error_message)
*)
let can_apply_rule rule ill_seq =
    match rule with
    | ILL_Axiom ->
        (* Axiom requires context with single atom matching goal *)
        (match ill_seq.context, ill_seq.goal with
         | [Litt a], Litt b when a = b -> (true, "")
         | _ -> (false, "Axiom rule requires context A and goal A"))
    
    | ILL_One ->
        (* One rule requires empty context and goal 1 *)
        (match ill_seq.context, ill_seq.goal with
         | [], One -> (true, "")
         | _ -> (false, "One rule requires empty context and goal 1"))
    
    | ILL_Top ->
        (* Top rule always applicable with goal ⊤ *)
        (match ill_seq.goal with
         | Top -> (true, "")
         | _ -> (false, "Top rule requires goal ⊤"))
    
    | ILL_Tensor ->
        (* Tensor rule requires goal A⊗B *)
        (match ill_seq.goal with
         | Tensor (_, _) -> (true, "")
         | _ -> (false, "Tensor rule requires goal A⊗B"))
    
    | ILL_Tensor_left ->
        (* Tensor left rule requires A⊗B in context *)
        let has_tensor = List.exists is_tensor ill_seq.context in
        if has_tensor then (true, "")
        else (false, "Tensor left rule requires A⊗B in context")
    
    | ILL_With_left_1 | ILL_With_left_2 ->
        (* With left rules require A&B in context *)
        let has_with = List.exists is_with ill_seq.context in
        if has_with then (true, "")
        else (false, "With left rule requires A&B in context")
    
    | ILL_With_right ->
        (* With right rule requires goal A&B *)
        (match ill_seq.goal with
         | With (_, _) -> (true, "")
         | _ -> (false, "With right rule requires goal A&B"))
    
    | ILL_Plus_left ->
        (* Plus left rule requires A⊕B in context *)
        let has_plus = List.exists is_plus ill_seq.context in
        if has_plus then (true, "")
        else (false, "Plus left rule requires A⊕B in context")
    
    | ILL_Plus_right_1 | ILL_Plus_right_2 ->
        (* Plus right rules require goal A⊕B *)
        (match ill_seq.goal with
         | Plus (_, _) -> (true, "")
         | _ -> (false, "Plus right rule requires goal A⊕B"))
    
    | ILL_Lollipop ->
        (* Lollipop rule requires goal A⊸B *)
        (match ill_seq.goal with
         | Lollipop (_, _) -> (true, "")
         | _ -> (false, "Lollipop rule requires goal A⊸B"))
    
    | ILL_Lollipop_left ->
        (* Lollipop left rule requires A⊸B in context *)
        let has_lollipop = List.exists is_lollipop ill_seq.context in
        if has_lollipop then (true, "")
        else (false, "Lollipop left rule requires A⊸B in context")
    
    | ILL_Cut ->
        (* Cut rule can always be applied *)
        (true, "")
    
    | ILL_Weakening ->
        (* Weakening rule: Γ ⊢ B / Γ,!A ⊢ B - can always weaken with !A *)
        (true, "")
    
    | ILL_Contraction ->
        (* Contraction rule: Γ,!A ⊢ B / Γ,!A,!A ⊢ B - needs !A in context *)
        let has_ofcourse = List.exists is_ofcourse ill_seq.context in
        if has_ofcourse then (true, "")
        else (false, "Contraction rule requires !A in context")
    
    | ILL_Dereliction ->
        (* Dereliction rule: Γ,!A ⊢ B / Γ,A ⊢ B - needs !A in context *)
        let has_ofcourse = List.exists is_ofcourse ill_seq.context in
        if has_ofcourse then (true, "")
        else (false, "Dereliction rule requires !A in context")
    
    | ILL_Promotion ->
        (* Promotion rule: !Γ ⊢ !A / !Γ ⊢ A - needs goal !A and all context must be !-formulas *)
        (match ill_seq.goal with
         | Ofcourse _ ->
             let all_exponential = List.for_all is_ofcourse ill_seq.context in
             if all_exponential then (true, "")
             else (false, "Promotion rule requires all context formulas to be exponential (!)")
         | _ -> (false, "Promotion rule requires goal !A"))

(* CONTEXT MANIPULATION HELPERS *)

(* Split context for tensor rule - simple implementation *)
let split_context_simple ctx =
    match ctx with
    | [] -> ([], [])
    | [f] -> ([f], [])
    | f1 :: rest -> ([f1], rest)

(* Split context based on provided comma position for tensor rule.
   @param ctx - Context formulas list
   @param comma_position - Position where Gamma ends (0-based)
   @return (gamma, delta) - Split context
*)
let split_context_at_position ctx comma_position =
    if comma_position < 0 || comma_position > List.length ctx then
        failwith "Invalid comma position for context split"
    else
        let ctx_array = Array.of_list ctx in
        let gamma = Array.sub ctx_array 0 comma_position |> Array.to_list in
        let delta = Array.sub ctx_array comma_position (Array.length ctx_array - comma_position) |> Array.to_list in
        (gamma, delta)

(* Split context for tensor rule with context split information.
   @param ctx - Context formulas list
   @param context_split_opt - Optional context split position list
   @return (gamma, delta) - Split context
*)
let split_context_for_tensor ctx context_split_opt =
    match context_split_opt with
    | Some [comma_pos] -> split_context_at_position ctx comma_pos
    | Some [] -> ([], ctx)  (* Empty Gamma case *)
    | Some _ -> failwith "Invalid context split format for tensor rule"
    | None -> split_context_simple ctx  (* Fallback to simple split *)

(* Split context for cut rule at specified position.
   @param ctx - Context formulas list
   @param cut_position - Position to split context (0-based)
   @return (gamma, delta) - Split context where cut formula will be inserted between
*)
let split_context_for_cut ctx cut_position =
    if cut_position < 0 || cut_position > List.length ctx then
        failwith "Invalid cut position for context split"
    else
        let ctx_array = Array.of_list ctx in
        let gamma = Array.sub ctx_array 0 cut_position |> Array.to_list in
        let delta = Array.sub ctx_array cut_position (Array.length ctx_array - cut_position) |> Array.to_list in
        (gamma, delta)

(* Expand tensor formula in context: A⊗B becomes A,B *)
let expand_tensor_in_context ctx =
    let rec expand_first_tensor acc = function
        | [] -> acc
        | Tensor (a, b) :: rest -> acc @ [a; b] @ rest
        | f :: rest -> expand_first_tensor (acc @ [f]) rest
    in
    expand_first_tensor [] ctx

(* Extract first lollipop formula from context *)
let extract_lollipop_from_context ctx =
    let rec extract acc = function
        | [] -> (acc, None)
        | Lollipop (a, b) :: rest -> (acc @ rest, Some (Lollipop (a, b)))
        | f :: rest -> extract (acc @ [f]) rest
    in
    extract [] ctx

(* Extract first with formula from context *)
let extract_with_from_context ctx =
    let rec extract acc = function
        | [] -> (acc, None)
        | With (a, b) :: rest -> (acc @ rest, Some (With (a, b)))
        | f :: rest -> extract (acc @ [f]) rest
    in
    extract [] ctx

(* Helper function to split list at specific position *)
let split_list_at_position list pos =
    let rec split acc n = function
        | [] -> failwith ("Position " ^ string_of_int pos ^ " out of bounds")
        | h :: t when n = 0 -> (List.rev acc, h, t)
        | h :: t -> split (h :: acc) (n - 1) t
    in
    split [] pos list

(* RULE APPLICATION *)

(* Apply an ILL rule to a sequent and generate premise sequents.
   @param rule_req - Rule request with parameters
   @param ill_seq - Sequent to apply rule to
   @return ill_sequent list - Generated premise sequents
*)
let apply_rule_to_sequent rule_req ill_seq =
    match rule_req.rule with
    | ILL_Axiom ->
        (* Axiom has no premises *)
        []
    
    | ILL_One ->
        (* One rule has no premises *)
        []
    
    | ILL_Top ->
        (* Top rule has no premises *)
        []
    
    | ILL_Tensor ->
        (* Tensor rule: Γ,Δ ⊢ A⊗B becomes Γ ⊢ A and Δ ⊢ B *)
        (match ill_seq.goal with
         | Tensor (a, b) ->
             (* Split context between the two premises using comma selection if available *)
             let ctx1, ctx2 = split_context_for_tensor ill_seq.context rule_req.context_split in
             [{ context = ctx1; goal = a }; { context = ctx2; goal = b }]
         | _ -> [])
    
    | ILL_Tensor_left ->
        (* Tensor left: Γ,A⊗B,Δ ⊢ C becomes Γ,A,B,Δ ⊢ C *)
        let updated_context = expand_tensor_in_context ill_seq.context in
        [{ context = updated_context; goal = ill_seq.goal }]
    
    | ILL_With_left_1 ->
        (* With left 1: Γ,A&B ⊢ C becomes Γ,A ⊢ C *)
        let (ctx_without_with, with_formula) = extract_with_from_context ill_seq.context in
        (match with_formula with
         | Some (With (a, _)) ->
             [{ context = a :: ctx_without_with; goal = ill_seq.goal }]
         | _ -> [])
    
    | ILL_With_left_2 ->
        (* With left 2: Γ,A&B ⊢ C becomes Γ,B ⊢ C *)
        let (ctx_without_with, with_formula) = extract_with_from_context ill_seq.context in
        (match with_formula with
         | Some (With (_, b)) ->
             [{ context = b :: ctx_without_with; goal = ill_seq.goal }]
         | _ -> [])
    
    | ILL_With_right ->
        (* With right: Γ ⊢ A&B becomes Γ ⊢ A and Γ ⊢ B *)
        (match ill_seq.goal with
         | With (a, b) ->
             [{ context = ill_seq.context; goal = a };
              { context = ill_seq.context; goal = b }]
         | _ -> [])
    
    | ILL_Plus_left ->
        (* Plus left: Γ,A⊕B,Δ ⊢ C becomes Γ,A,Δ ⊢ C and Γ,B,Δ ⊢ C *)
        let rec extract_plus acc = function
            | [] -> (acc, None)
            | Plus (a, b) :: rest -> (acc @ rest, Some (Plus (a, b)))
            | f :: rest -> extract_plus (acc @ [f]) rest
        in
        let (ctx_without_plus, plus_formula) = extract_plus [] ill_seq.context in
        (match plus_formula with
         | Some (Plus (a, b)) ->
             [{ context = a :: ctx_without_plus; goal = ill_seq.goal };
              { context = b :: ctx_without_plus; goal = ill_seq.goal }]
         | _ -> [])
    
    | ILL_Plus_right_1 ->
        (* Plus right 1: Γ ⊢ A⊕B becomes Γ ⊢ A *)
        (match ill_seq.goal with
         | Plus (a, _) ->
             [{ context = ill_seq.context; goal = a }]
         | _ -> [])
    
    | ILL_Plus_right_2 ->
        (* Plus right 2: Γ ⊢ A⊕B becomes Γ ⊢ B *)
        (match ill_seq.goal with
         | Plus (_, b) ->
             [{ context = ill_seq.context; goal = b }]
         | _ -> [])
    
    | ILL_Lollipop ->
        (* Lollipop: Γ ⊢ A⊸B becomes Γ,A ⊢ B *)
        (match ill_seq.goal with
         | Lollipop (a, b) ->
             [{ context = a :: ill_seq.context; goal = b }]
         | _ -> [])
    
    | ILL_Lollipop_left ->
        (* Lollipop left: Γ,A⊸B,Δ ⊢ C becomes Γ ⊢ A and Δ,B ⊢ C *)
        let (ctx_without_lollipop, lollipop_formula) = extract_lollipop_from_context ill_seq.context in
        (match lollipop_formula with
         | Some (Lollipop (a, b)) ->
             (* Need to properly split context into Gamma and Delta *)
             let gamma, delta = split_context_simple ctx_without_lollipop in
             [{ context = gamma; goal = a };
              { context = delta @ [b]; goal = ill_seq.goal }]
         | _ -> [])
    
    | ILL_Cut ->
        (* Cut rule: Γ,Δ ⊢ C becomes Γ ⊢ A and Δ,A ⊢ C *)
        (match rule_req.cut_formula, rule_req.cut_position with
         | Some cut_formula, Some cut_pos ->
             let gamma, delta = split_context_for_cut ill_seq.context cut_pos in
             [{ context = gamma; goal = cut_formula };
              { context = delta @ [cut_formula]; goal = ill_seq.goal }]
         | _ ->
             (* Fallback: split at beginning if no position specified *)
             let cut_formula = match rule_req.cut_formula with
                 | Some f -> f
                 | None -> Litt "A"  (* Default cut formula *)
             in
             [{ context = []; goal = cut_formula };
              { context = ill_seq.context @ [cut_formula]; goal = ill_seq.goal }])
    
    | ILL_Weakening ->
        (* Weakening: Γ,!A ⊢ B becomes Γ ⊢ B *)
        (match rule_req.formula_position with
         | Some pos when pos >= 0 && pos < List.length ill_seq.context ->
             let (gamma_before, _, gamma_after) = split_list_at_position ill_seq.context pos in
             [{ context = gamma_before @ gamma_after; goal = ill_seq.goal }]
         | _ -> [])
    
    | ILL_Contraction ->
        (* Contraction: Γ,!A ⊢ B becomes Γ,!A,!A ⊢ B *)
        (match rule_req.formula_position with
         | Some pos when pos >= 0 && pos < List.length ill_seq.context ->
             let (gamma_before, exp_formula, gamma_after) = split_list_at_position ill_seq.context pos in
             [{ context = gamma_before @ [exp_formula; exp_formula] @ gamma_after; goal = ill_seq.goal }]
         | _ -> [])
    
    | ILL_Dereliction ->
        (* Dereliction: Γ,!A ⊢ B becomes Γ,A ⊢ B *)
        (match rule_req.formula_position with
         | Some pos when pos >= 0 && pos < List.length ill_seq.context ->
             let (gamma_before, exp_formula, gamma_after) = split_list_at_position ill_seq.context pos in
             (match exp_formula with
              | Ofcourse inner_formula ->
                  [{ context = gamma_before @ [inner_formula] @ gamma_after; goal = ill_seq.goal }]
              | _ -> [])
         | _ -> [])
    
    | ILL_Promotion ->
        (* Promotion: !Γ ⊢ !A becomes !Γ ⊢ A *)
        (match ill_seq.goal with
         | Ofcourse inner_formula ->
             [{ context = ill_seq.context; goal = inner_formula }]
         | _ -> [])


(* JSON PARSING *)

(* Parse ILL rule from JSON representation.
   @param json - JSON object containing rule information
   @return ill_rule - Parsed rule
*)
let rule_from_json json =
    match json with
    | `Assoc assoc_list ->
        (match List.assoc_opt "rule" assoc_list with
         | Some (`String "ill_axiom") -> ILL_Axiom
         | Some (`String "ill_one") -> ILL_One
         | Some (`String "ill_top") -> ILL_Top
         | Some (`String "ill_tensor_right") -> ILL_Tensor
         | Some (`String "ill_tensor") -> ILL_Tensor
         | Some (`String "ill_tensor_left") -> ILL_Tensor_left
         | Some (`String "ill_with_left_1") -> ILL_With_left_1
         | Some (`String "ill_with_left_2") -> ILL_With_left_2
         | Some (`String "ill_with_right") -> ILL_With_right
         | Some (`String "ill_plus_left") -> ILL_Plus_left
         | Some (`String "ill_plus_right_1") -> ILL_Plus_right_1
         | Some (`String "ill_plus_right_2") -> ILL_Plus_right_2
         | Some (`String "ill_lollipop") -> ILL_Lollipop
         | Some (`String "ill_lollipop_right") -> ILL_Lollipop
         | Some (`String "ill_lollipop_left") -> ILL_Lollipop_left
         | Some (`String "ill_cut") -> ILL_Cut
         | Some (`String "ill_weakening") -> ILL_Weakening
         | Some (`String "ill_contraction") -> ILL_Contraction
         | Some (`String "ill_dereliction") -> ILL_Dereliction
         | Some (`String "ill_promotion") -> ILL_Promotion
         | _ -> failwith "Unknown ILL rule")
    | _ -> failwith "Invalid rule JSON format"

(* Parse complete ILL rule request from JSON.
   @param json - JSON object from frontend  
   @return ill_rule_request - Parsed rule request
*)
let from_json_deprecated json =
    try
        let rule = rule_from_json json in
        let formula_position = 
            try
                match List.assoc "formulaPosition" (match json with `Assoc l -> l | _ -> []) with
                | `Int pos -> Some pos
                | _ -> None
            with _ -> None
        in
        let side =
            try
                match List.assoc "side" (match json with `Assoc l -> l | _ -> []) with
                | `String s -> Some s
                | _ -> None
            with _ -> None
        in
        let sequent_side =
            try
                match List.assoc "sequentSide" (match json with `Assoc l -> l | _ -> []) with
                | `String s -> Some s
                | _ -> None
            with _ -> None
        in
        let cut_formula = 
            try
                let cut_json = List.assoc "cutFormula" (match json with `Assoc l -> l | _ -> []) in
                Some (Raw_sequent.json_to_raw_formula cut_json |> convert_raw_formula_to_ill)
            with _ -> None
        in
        let cut_position =
            try
                match List.assoc "cutPosition" (match json with `Assoc l -> l | _ -> []) with
                | `Int pos -> Some pos
                | _ -> None
            with _ -> None
        in
        {
            rule = rule;
            formula_position = formula_position;
            side = side;
            context_split =
                (try
                    match List.assoc "contextSplit" (match json with `Assoc l -> l | _ -> []) with
                    | `List int_list ->
                        let positions = List.map (function
                            | `Int i -> i
                            | _ -> failwith "Invalid context split position")
                            int_list in
                        Some positions
                    | _ -> None
                with _ -> None);
            sequent_side = sequent_side;
            cut_formula = cut_formula;
            cut_position = cut_position;
        }
    with
    | ILL_Rule_Json_Exception msg -> failwith msg
    | _ -> failwith "Failed to parse ILL rule request"

(* JSON SERIALIZATION *)

(* Convert ILL rule to JSON representation.
   @param rule - ILL rule
   @return Yojson.Basic.t - JSON representation
*)
let rule_to_json = function
    | ILL_Axiom -> `String "ill_axiom"
    | ILL_One -> `String "ill_one"
    | ILL_Top -> `String "ill_top"
    | ILL_Tensor -> `String "ill_tensor_right"
    | ILL_Tensor_left -> `String "ill_tensor_left"
    | ILL_With_left_1 -> `String "ill_with_left_1"
    | ILL_With_left_2 -> `String "ill_with_left_2"
    | ILL_With_right -> `String "ill_with_right"
    | ILL_Plus_left -> `String "ill_plus_left"
    | ILL_Plus_right_1 -> `String "ill_plus_right_1"
    | ILL_Plus_right_2 -> `String "ill_plus_right_2"
    | ILL_Lollipop -> `String "ill_lollipop"
    | ILL_Lollipop_left -> `String "ill_lollipop_left"
    | ILL_Cut -> `String "ill_cut"
    | ILL_Weakening -> `String "ill_weakening"
    | ILL_Contraction -> `String "ill_contraction"
    | ILL_Dereliction -> `String "ill_dereliction"
    | ILL_Promotion -> `String "ill_promotion"


(* RULE INFERENCE *)

(* Infer which ILL rule should be applied based on the clicked formula.
   This is called when the user clicks on a formula in the frontend.
   @param ill_seq - Current sequent
   @param formula_pos - Position of clicked formula
   @return ill_rule_request option - Inferred rule or None
*)
(* Infer which ILL rule to apply based on clicked formula and sequent side.
   @param rule_req - Original rule request from frontend
   @param ill_seq - Current sequent
   @return ill_rule_request - Updated rule request with correct rule
*)
let rec infer_rule_from_side_and_formula rule_req ill_seq =
    match rule_req.sequent_side with
    | Some "left" ->
        (* User clicked on formula in context (left side) *)
        infer_left_rule rule_req ill_seq
    | Some "right" ->
        (* User clicked on goal formula (right side) *)
        infer_right_rule rule_req ill_seq  
    | _ ->
        (* Fallback to original rule *)
        rule_req

(* Infer which left rule to apply based on the clicked formula in context *)
and infer_left_rule rule_req ill_seq =
    match rule_req.formula_position with
    | Some pos when pos < List.length ill_seq.context ->
        let clicked_formula = List.nth ill_seq.context pos in
        (match clicked_formula with
         | Tensor (_, _) -> 
             { rule_req with rule = ILL_Tensor_left }
         | With (_, _) -> 
             (* Only infer rule if frontend hasn't already specified a specific with rule *)
             (match rule_req.rule with
              | ILL_With_left_1 | ILL_With_left_2 -> 
                  (* Frontend already specified specific rule, preserve it *)
                  rule_req
              | _ -> 
                  (* For generic or unknown rules, try to infer from position/side info *)
                  (* For now, default to with_left_1 but this could be improved *)
                  { rule_req with rule = ILL_With_left_1 })
         | Plus (_, _) -> 
             { rule_req with rule = ILL_Plus_left }
         | Lollipop (_, _) -> 
             { rule_req with rule = ILL_Lollipop_left }
         | Litt _ ->
             (* Could be axiom if context has single atom matching goal *)
             { rule_req with rule = ILL_Axiom }
         | Ofcourse _ ->
             (* Exponential formula in context - could be weakening, contraction, or dereliction *)
             (* Default to dereliction for now, frontend should specify exact rule *)
             { rule_req with rule = ILL_Dereliction }
         | _ ->
             rule_req)  (* No applicable left rule *)
    | _ -> rule_req

(* Infer which right rule to apply based on the goal formula *)
and infer_right_rule rule_req ill_seq =
    match ill_seq.goal with
    | One -> { rule_req with rule = ILL_One }
    | Top -> { rule_req with rule = ILL_Top }
    | Tensor (_, _) -> { rule_req with rule = ILL_Tensor }
    | With (_, _) -> { rule_req with rule = ILL_With_right }
    | Plus (_, _) ->
        (* If frontend already chose a specific plus rule, keep it *)
        (match rule_req.rule with
         | ILL_Plus_right_1 | ILL_Plus_right_2 -> rule_req
         | _ -> { rule_req with rule = ILL_Plus_right_1 }) (* Default for backward compatibility *)
    | Lollipop (_, _) -> { rule_req with rule = ILL_Lollipop }
    | Litt _ -> { rule_req with rule = ILL_Axiom }
    | Ofcourse _ -> { rule_req with rule = ILL_Promotion }

(* RULE DESCRIPTIONS *)

(* Get human-readable description of an ILL rule.
   @param rule - ILL rule
   @return string - Description for UI display
*)
let rule_description = function
    | ILL_Axiom -> "Axiom rule: A ⊢ A"
    | ILL_One -> "One introduction: ⊢ 1"  
    | ILL_Top -> "Top introduction: Γ ⊢ ⊤"
    | ILL_Tensor -> "Tensor introduction: Γ,Δ ⊢ A⊗B / Γ ⊢ A & Δ ⊢ B"
    | ILL_Tensor_left -> "Tensor elimination: Γ,A⊗B,Δ ⊢ C / Γ,A,B,Δ ⊢ C"
    | ILL_With_left_1 -> "With left 1: Γ,A&B ⊢ C / Γ,A ⊢ C"
    | ILL_With_left_2 -> "With left 2: Γ,A&B ⊢ C / Γ,B ⊢ C"
    | ILL_With_right -> "With right: Γ ⊢ A&B / Γ ⊢ A & Γ ⊢ B"
    | ILL_Plus_left -> "Plus left: Γ,A⊕B,Δ ⊢ C / Γ,A,Δ ⊢ C & Γ,B,Δ ⊢ C"
    | ILL_Plus_right_1 -> "Plus right 1: Γ ⊢ A⊕B / Γ ⊢ A"
    | ILL_Plus_right_2 -> "Plus right 2: Γ ⊢ A⊕B / Γ ⊢ B"
    | ILL_Lollipop -> "Lollipop introduction: Γ ⊢ A⊸B / Γ,A ⊢ B"
    | ILL_Lollipop_left -> "Lollipop elimination: Γ ⊢ A & Δ,B ⊢ C / Γ,A⊸B,Δ ⊢ C"
    | ILL_Cut -> "Cut rule: Γ,Δ ⊢ C / Γ ⊢ A & Δ,A ⊢ C"
    | ILL_Weakening -> "Weakening: Γ ⊢ B / Γ,!A ⊢ B"
    | ILL_Contraction -> "Contraction: Γ,!A ⊢ B / Γ,!A,!A ⊢ B"
    | ILL_Dereliction -> "Dereliction: Γ,!A ⊢ B / Γ,A ⊢ B"
    | ILL_Promotion -> "Promotion: !Γ ⊢ !A / !Γ ⊢ A"

(* Get rule name for display in proof trees.
   @param rule - ILL rule
   @return string - Short name for proof display
*)
let rule_name = function
    | ILL_Axiom -> "ax"
    | ILL_One -> "1"
    | ILL_Top -> "⊤"
    | ILL_Tensor -> "⊗"
    | ILL_Tensor_left -> "⊗L"
    | ILL_With_left_1 -> "&L₁"
    | ILL_With_left_2 -> "&L₂"
    | ILL_With_right -> "&R"
    | ILL_Plus_left -> "+L"
    | ILL_Plus_right_1 -> "⊕₁"
    | ILL_Plus_right_2 -> "⊕₂"
    | ILL_Lollipop -> "⊸"
    | ILL_Lollipop_left -> "⊸L"
    | ILL_Cut -> "cut"
    | ILL_Weakening -> "!w"
    | ILL_Contraction -> "!c"
    | ILL_Dereliction -> "!d"
    | ILL_Promotion -> "!p"

(* JSON SERIALIZATION *)

(* Convert ILL rule to JSON string for frontend communication.
   @param rule - ILL rule type
   @return string - Rule name for JSON serialization
*)
let rule_to_json_string = function
    | ILL_Axiom -> "ill_axiom"
    | ILL_One -> "ill_one"
    | ILL_Top -> "ill_top"
    | ILL_Tensor -> "ill_tensor_right"
    | ILL_Tensor_left -> "ill_tensor_left"
    | ILL_With_left_1 -> "ill_with_left_1"
    | ILL_With_left_2 -> "ill_with_left_2"
    | ILL_With_right -> "ill_with_right"
    | ILL_Plus_left -> "ill_plus_left"
    | ILL_Plus_right_1 -> "ill_plus_right_1"
    | ILL_Plus_right_2 -> "ill_plus_right_2"
    | ILL_Lollipop -> "ill_lollipop_right"
    | ILL_Lollipop_left -> "ill_lollipop_left"
    | ILL_Cut -> "ill_cut"
    | ILL_Weakening -> "ill_weakening"
    | ILL_Contraction -> "ill_contraction"
    | ILL_Dereliction -> "ill_dereliction"
    | ILL_Promotion -> "ill_promotion"

(* Convert JSON string to ILL rule type.
   @param rule_str - Rule name from JSON
   @return ill_rule - Parsed ILL rule
   @raises ILL_Rule_Json_Exception for unknown rules
*)
let rule_from_json_string = function
    | "ill_axiom" -> ILL_Axiom
    | "ill_one" -> ILL_One
    | "ill_top" -> ILL_Top
    | "ill_tensor_right" -> ILL_Tensor
    | "ill_tensor_left" -> ILL_Tensor_left
    | "ill_with_left_1" -> ILL_With_left_1
    | "ill_with_left_2" -> ILL_With_left_2
    | "ill_with_right" -> ILL_With_right
    | "ill_plus_left" -> ILL_Plus_left
    | "ill_plus_right_1" -> ILL_Plus_right_1
    | "ill_plus_right_2" -> ILL_Plus_right_2
    | "ill_lollipop_right" -> ILL_Lollipop
    | "ill_lollipop_left" -> ILL_Lollipop_left
    | "ill_cut" -> ILL_Cut
    | "ill_weakening" -> ILL_Weakening
    | "ill_contraction" -> ILL_Contraction
    | "ill_dereliction" -> ILL_Dereliction
    | "ill_promotion" -> ILL_Promotion
    | unknown -> raise (ILL_Rule_Json_Exception ("Unknown ILL rule: " ^ unknown))

(* Convert ILL rule request to JSON representation.
   @param rule_req - ILL rule request
   @return Yojson.Basic.t - JSON representation
*)
let to_json rule_req =
    let rule_json = `String (rule_to_json_string rule_req.rule) in
    let base_fields = [("rule", rule_json)] in
    
    (* Add optional fields if they exist *)
    let fields_with_position = match rule_req.formula_position with
        | Some pos -> ("formulaPosition", `Int pos) :: base_fields
        | None -> base_fields
    in
    
    let fields_with_side = match rule_req.side with
        | Some s -> ("side", `String s) :: fields_with_position
        | None -> fields_with_position
    in
    
    let fields_with_context_split = match rule_req.context_split with
        | Some split_list -> ("contextSplit", `List (List.map (fun i -> `Int i) split_list)) :: fields_with_side
        | None -> fields_with_side
    in
    
    let fields_with_sequent_side = match rule_req.sequent_side with
        | Some ss -> ("sequentSide", `String ss) :: fields_with_context_split
        | None -> fields_with_context_split
    in
    
    let fields_with_cut_formula = match rule_req.cut_formula with
        | Some f -> ("cutFormula", Raw_sequent.raw_formula_to_json (ill_formula_to_raw f)) :: fields_with_sequent_side
        | None -> fields_with_sequent_side
    in
    
    let final_fields = match rule_req.cut_position with
        | Some pos -> ("cutPosition", `Int pos) :: fields_with_cut_formula
        | None -> fields_with_cut_formula
    in
    
    `Assoc final_fields

(* Parse ILL rule request from JSON representation.
   @param json - JSON object from frontend
   @return ill_rule_request - Parsed rule request
   @raises ILL_Rule_Json_Exception for malformed JSON
*)
let from_json json =
    try
        (* Extract required rule field *)
        let rule_str = match Yojson.Basic.Util.member "rule" json with
            | `String s -> s
            | _ -> raise (ILL_Rule_Json_Exception "rule field must be a string")
        in
        let rule = rule_from_json_string rule_str in
        
        (* Extract optional fields *)
        let formula_position = match Yojson.Basic.Util.member "formulaPosition" json with
            | `Int pos -> Some pos
            | `Null -> None
            | _ -> raise (ILL_Rule_Json_Exception "formulaPosition must be an integer or null")
        in
        
        let side = match Yojson.Basic.Util.member "side" json with
            | `String s -> Some s
            | `Null -> None
            | _ -> raise (ILL_Rule_Json_Exception "side must be a string or null")
        in
        
        let context_split = match Yojson.Basic.Util.member "contextSplit" json with
            | `List split_list -> 
                Some (List.map (function 
                    | `Int i -> i 
                    | _ -> raise (ILL_Rule_Json_Exception "contextSplit must be list of integers")) split_list)
            | `Null -> None
            | _ -> raise (ILL_Rule_Json_Exception "contextSplit must be a list or null")
        in
        
        let sequent_side = match Yojson.Basic.Util.member "sequentSide" json with
            | `String s -> Some s
            | `Null -> None
            | _ -> raise (ILL_Rule_Json_Exception "sequentSide must be a string or null")
        in
        
        let cut_formula = match Yojson.Basic.Util.member "cutFormula" json with
            | `Null -> None
            | formula_json -> 
                let raw_formula = Raw_sequent.json_to_raw_formula formula_json in
                Some (convert_raw_formula_to_ill raw_formula)
        in
        
        let cut_position = match Yojson.Basic.Util.member "cutPosition" json with
            | `Int pos -> Some pos
            | `Null -> None
            | _ -> raise (ILL_Rule_Json_Exception "cutPosition must be an integer or null")
        in
        
        {
            rule = rule;
            formula_position = formula_position;
            side = side;
            context_split = context_split;
            sequent_side = sequent_side;
            cut_formula = cut_formula;
            cut_position = cut_position;
        }
    with
    | Yojson.Basic.Util.Type_error (msg, _) -> raise (ILL_Rule_Json_Exception ("JSON type error: " ^ msg))
    | exn -> raise (ILL_Rule_Json_Exception ("JSON parsing error: " ^ (Printexc.to_string exn)))