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
   
   Removed from classical LL:
   - Par rule (no ⅋ connective)
   - With rule has left and right rules
   - All exponential rules (!, ?)
*)

open Ill_sequent

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

(* Rule request data structure.
   Contains the rule to apply and additional parameters like formula position.
*)
type ill_rule_request = {
    rule: ill_rule;                    (* Which rule to apply *)
    formula_position: int option;      (* Position of main formula in sequent *)
    side: string option;              (* For rules with choices (left/right) *)
    context_split: int list option;   (* For tensor rule context splitting *)
    sequent_side: string option;     (* Which side of turnstile was clicked (left/right) *)
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

(* CONTEXT MANIPULATION HELPERS *)

(* Split context for tensor rule - simple implementation *)
let split_context_simple ctx =
    match ctx with
    | [] -> ([], [])
    | [f] -> ([f], [])
    | f1 :: rest -> ([f1], rest)

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
             (* Split context between the two premises *)
             let ctx1, ctx2 = split_context_simple ill_seq.context in
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
         | Some (`String "axiom") -> ILL_Axiom  (* Backward compatibility *)
         | Some (`String "ill_one") -> ILL_One
         | Some (`String "one") -> ILL_One  (* Backward compatibility *)
         | Some (`String "ill_top") -> ILL_Top
         | Some (`String "top") -> ILL_Top  (* Backward compatibility *)
         | Some (`String "ill_tensor_right") -> ILL_Tensor
         | Some (`String "ill_tensor") -> ILL_Tensor  (* Backward compatibility *)
         | Some (`String "tensor_right") -> ILL_Tensor  (* Backward compatibility *)
         | Some (`String "tensor") -> ILL_Tensor  (* Backward compatibility *)
         | Some (`String "ill_tensor_left") -> ILL_Tensor_left
         | Some (`String "tensor_left") -> ILL_Tensor_left  (* Backward compatibility *)
         | Some (`String "ill_with_left_1") -> ILL_With_left_1
         | Some (`String "with_left_1") -> ILL_With_left_1  (* Backward compatibility *)
         | Some (`String "ill_with_left_2") -> ILL_With_left_2
         | Some (`String "with_left_2") -> ILL_With_left_2  (* Backward compatibility *)
         | Some (`String "ill_with_right") -> ILL_With_right
         | Some (`String "with_right") -> ILL_With_right  (* Backward compatibility *)
         | Some (`String "ill_plus_left") -> ILL_Plus_left
         | Some (`String "plus_left") -> ILL_Plus_left  (* Backward compatibility *)
         | Some (`String "ill_plus_right_1") -> ILL_Plus_right_1
         | Some (`String "plus_right_1") -> ILL_Plus_right_1  (* Backward compatibility *)
         | Some (`String "ill_plus_right_2") -> ILL_Plus_right_2
         | Some (`String "plus_right_2") -> ILL_Plus_right_2  (* Backward compatibility *)
         | Some (`String "plus_right") -> ILL_Plus_right_1  (* Backward compatibility *)
         | Some (`String "ill_lollipop") -> ILL_Lollipop
         | Some (`String "lollipop") -> ILL_Lollipop  (* Backward compatibility *)
         | Some (`String "ill_lollipop_left") -> ILL_Lollipop_left
         | Some (`String "lollipop_left") -> ILL_Lollipop_left  (* Backward compatibility *)
         | Some (`String "with") -> ILL_With_left_1  (* Generic "with" for rule inference *)
         | _ -> raise (ILL_Rule_Json_Exception "Unknown ILL rule"))
    | _ -> raise (ILL_Rule_Json_Exception "Invalid rule JSON format")

(* Parse complete ILL rule request from JSON.
   @param json - JSON object from frontend
   @return ill_rule_request - Parsed rule request
*)
let from_json json =
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
        {
            rule = rule;
            formula_position = formula_position;
            side = side;
            context_split = None;  (* TODO: Parse context split information *)
            sequent_side = sequent_side;
        }
    with
    | ILL_Rule_Json_Exception msg -> raise (ILL_Rule_Json_Exception msg)
    | _ -> raise (ILL_Rule_Json_Exception "Failed to parse ILL rule request")

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

(* Convert ILL rule request to JSON representation.
   @param rule_req - ILL rule request
   @return Yojson.Basic.t - JSON representation
*)
let to_json rule_req =
    let base_assoc = [("rule", rule_to_json rule_req.rule)] in
    let with_pos = match rule_req.formula_position with
        | Some pos -> ("formulaPosition", `Int pos) :: base_assoc
        | None -> base_assoc
    in
    let with_side = match rule_req.side with
        | Some s -> ("side", `String s) :: with_pos
        | None -> with_pos
    in
    `Assoc with_side

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
             (* Default to with_left_1, frontend can specify specific rule *)
             { rule_req with rule = ILL_With_left_1 }
         | Plus (_, _) -> 
             { rule_req with rule = ILL_Plus_left }
         | Lollipop (_, _) -> 
             { rule_req with rule = ILL_Lollipop_left }
         | Litt _ ->
             (* Could be axiom if context has single atom matching goal *)
             { rule_req with rule = ILL_Axiom }
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