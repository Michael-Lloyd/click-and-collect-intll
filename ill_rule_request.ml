(* INTUITIONISTIC LINEAR LOGIC RULE REQUEST HANDLING
   
   This module defines the rules available in ILL and handles parsing rule requests
   from the frontend. ILL has a more restricted set of rules compared to classical LL.
   
   Available ILL rules:
   - Axiom: A ⊢ A (identity)
   - One: ⊢ 1 (multiplicative unit introduction)
   - Top: Γ ⊢ ⊤ (additive unit introduction)  
   - Tensor: Γ,Δ ⊢ A⊗B / Γ ⊢ A & Δ ⊢ B (multiplicative conjunction)
   - Plus_left: Γ ⊢ A⊕B / Γ ⊢ A (additive disjunction left)
   - Plus_right: Γ ⊢ A⊕B / Γ ⊢ B (additive disjunction right)
   - Lollipop: Γ ⊢ A⊸B / Γ,A ⊢ B (linear implication introduction)
   
   Removed from classical LL:
   - Par rule (no ⅋ connective)
   - With rule (no & connective)
   - All exponential rules (!, ?)
*)

open Ill_sequent

(* ILL inference rule types.
   Each rule corresponds to an introduction rule for the respective connective.
*)
type ill_rule = 
    | ILL_Axiom
    | ILL_One
    | ILL_Top
    | ILL_Tensor
    | ILL_Plus_left
    | ILL_Plus_right
    | ILL_Lollipop

(* Rule request data structure.
   Contains the rule to apply and additional parameters like formula position.
*)
type ill_rule_request = {
    rule: ill_rule;                    (* Which rule to apply *)
    formula_position: int option;      (* Position of main formula in sequent *)
    side: string option;              (* For rules with choices (left/right) *)
    context_split: int list option;   (* For tensor rule context splitting *)
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
    
    | ILL_Plus_left | ILL_Plus_right ->
        (* Plus rules require goal A⊕B *)
        (match ill_seq.goal with
         | Plus (_, _) -> (true, "")
         | _ -> (false, "Plus rule requires goal A⊕B"))
    
    | ILL_Lollipop ->
        (* Lollipop rule requires goal A⊸B *)
        (match ill_seq.goal with
         | Lollipop (_, _) -> (true, "")
         | _ -> (false, "Lollipop rule requires goal A⊸B"))

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
             (* TODO: Implement context splitting logic *)
             (* For now, return stub premises *)
             [{ context = []; goal = a }; { context = []; goal = b }]
         | _ -> [])
    
    | ILL_Plus_left ->
        (* Plus left: Γ ⊢ A⊕B becomes Γ ⊢ A *)
        (match ill_seq.goal with
         | Plus (a, _) ->
             [{ context = ill_seq.context; goal = a }]
         | _ -> [])
    
    | ILL_Plus_right ->
        (* Plus right: Γ ⊢ A⊕B becomes Γ ⊢ B *)
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

(* JSON PARSING *)

(* Parse ILL rule from JSON representation.
   @param json - JSON object containing rule information
   @return ill_rule - Parsed rule
*)
let rule_from_json json =
    (* TODO: Implement JSON parsing for ILL rules *)
    match json with
    | `Assoc assoc_list ->
        (match List.assoc_opt "rule" assoc_list with
         | Some (`String "axiom") -> ILL_Axiom
         | Some (`String "one") -> ILL_One
         | Some (`String "top") -> ILL_Top
         | Some (`String "tensor") -> ILL_Tensor
         | Some (`String "plus_left") -> ILL_Plus_left
         | Some (`String "plus_right") -> ILL_Plus_right
         | Some (`String "lollipop") -> ILL_Lollipop
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
        {
            rule = rule;
            formula_position = formula_position;
            side = side;
            context_split = None;  (* TODO: Parse context split information *)
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
    | ILL_Axiom -> `String "axiom"
    | ILL_One -> `String "one"
    | ILL_Top -> `String "top"
    | ILL_Tensor -> `String "tensor"
    | ILL_Plus_left -> `String "plus_left"
    | ILL_Plus_right -> `String "plus_right"
    | ILL_Lollipop -> `String "lollipop"

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
let infer_rule_from_click _ill_seq formula_pos =
    (* TODO: Implement rule inference logic *)
    (* For now, return a simple axiom rule *)
    Some {
        rule = ILL_Axiom;
        formula_position = Some formula_pos;
        side = None;
        context_split = None;
    }

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
    | ILL_Plus_left -> "Plus left: Γ ⊢ A⊕B / Γ ⊢ A"
    | ILL_Plus_right -> "Plus right: Γ ⊢ A⊕B / Γ ⊢ B"
    | ILL_Lollipop -> "Lollipop introduction: Γ ⊢ A⊸B / Γ,A ⊢ B"

(* Get rule name for display in proof trees.
   @param rule - ILL rule
   @return string - Short name for proof display
*)
let rule_name = function
    | ILL_Axiom -> "ax"
    | ILL_One -> "1"
    | ILL_Top -> "⊤"
    | ILL_Tensor -> "⊗"
    | ILL_Plus_left -> "⊕₁"
    | ILL_Plus_right -> "⊕₂"
    | ILL_Lollipop -> "⊸"