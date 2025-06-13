# Backend Implementation Plan: Supporting Left/Right Distinction for ILL

## Current Backend Analysis

### ILL Left Rules Are Already Implemented! ✅

**Good News**: The backend already has comprehensive support for ILL left rules:

- **`ILL_Tensor_left`** - Tensor elimination: `Γ,A⊗B,Δ ⊢ C / Γ,A,B,Δ ⊢ C`
- **`ILL_Lollipop_left`** - Lollipop elimination: `Γ,A⊸B,Δ ⊢ C / Γ,Δ ⊢ A & B,Γ,Δ ⊢ C`

These are defined in `ill_rule_request.ml:27-36` and fully implemented in `ill_apply_rule.ml:174-364`.

### Current Backend Architecture

**Key Backend Files:**
- `main.ml:129-140` - Route to ILL vs LL rule application based on `intuitionisticMode`
- `ill_apply_rule.ml` - Complete ILL rule application logic
- `ill_rule_request.ml` - ILL rule definitions and JSON parsing
- `ill_sequent.ml` - ILL sequent structure (`{context: formula list; goal: formula}`)

### Current JSON Interface

**Rule Request Structure** (`ill_rule_request.ml:40-46`):
```ocaml
type ill_rule_request = {
    rule: ill_rule;                    (* Which rule to apply *)
    formula_position: int option;      (* Position of main formula *)
    side: string option;              (* For rules with choices (left/right) *)
    context_split: int list option;   (* For tensor rule context splitting *)
}
```

**Current Rule Parsing** (`ill_rule_request.ml:206-251`):
```ocaml
let from_json json =
    let rule = rule_from_json json in
    let formula_position = (* Parse formulaPosition field *) in
    let side = (* Parse side field *) in  (* ALREADY EXISTS! *)
    {
        rule = rule;
        formula_position = formula_position;
        side = side;                    (* Already supported! *)
        context_split = None;
    }
```

## Problem Analysis

### Critical Issue: How to Trigger Left Rules?

The problem is **not** that left rules are missing - they exist and work correctly. The problem is **how to trigger them** from the frontend:

1. **Current Logic**: When user clicks on `A⊗B` in the context, how does the backend know to apply `ILL_Tensor_left` instead of trying to apply a right rule?

2. **Rule Inference Gap**: The `infer_rule_from_click()` function (`ill_rule_request.ml:294-302`) is not implemented - it always returns axiom rule.

3. **Missing Side Detection**: The frontend doesn't send which side of the turnstile was clicked.

## Required Backend Changes

### 1. Enhanced Rule Request Processing

The JSON parsing already supports a `side` field, but we need to use it properly.

**Modify `ill_apply_rule.ml:124-150`** to process the new `sequentSide` field:

```ocaml
and apply_rule_with_exceptions request_as_json =
    try
        (* Extract rule request from JSON *)
        let rule_request_json = Request_utils.get_key request_as_json "ruleRequest" in
        let rule_request = from_json rule_request_json in
        
        (* NEW: Extract sequent side information *)
        let sequent_side = 
            try
                match List.assoc_opt "sequentSide" 
                    (match rule_request_json with `Assoc l -> l | _ -> []) with
                | Some (`String s) -> Some s
                | _ -> None
            with _ -> None
        in
        
        (* Extract sequent and convert to ILL format *)
        let sequent_json = Request_utils.get_key request_as_json "sequent" in
        let raw_sequent = Raw_sequent.from_json sequent_json in
        let ill_sequent = convert_raw_sequent_to_ill raw_sequent in
        
        (* NEW: Intelligently infer rule based on side and formula *)
        let final_rule_request = match sequent_side with
            | Some side -> infer_rule_from_side_and_formula rule_request ill_sequent side
            | None -> rule_request  (* Fallback to original logic *)
        in
        
        (* Apply the rule *)
        apply_ill_rule_internal final_rule_request ill_sequent []
```

### 2. Intelligent Rule Inference

**Add to `ill_rule_request.ml`** - Replace the stub `infer_rule_from_click()`:

```ocaml
(* Infer which ILL rule to apply based on clicked formula and sequent side.
   @param rule_req - Original rule request from frontend
   @param ill_seq - Current sequent
   @param side - "left" or "right" indicating which side of turnstile was clicked
   @return ill_rule_request - Updated rule request with correct rule
*)
let infer_rule_from_side_and_formula rule_req ill_seq side =
    match side with
    | "left" ->
        (* User clicked on formula in context (left side) *)
        infer_left_rule rule_req ill_seq
    | "right" ->
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
    | Plus (_, _) ->
        (* Need additional info to choose plus_left vs plus_right *)
        (* For now, default to left - frontend should specify *)
        { rule_req with rule = ILL_Plus_left }
    | Lollipop (_, _) -> { rule_req with rule = ILL_Lollipop }
    | Litt _ -> { rule_req with rule = ILL_Axiom }
```

### 3. Enhanced Rule Application Logic

**Modify `ill_apply_rule.ml:158-184`** to use position information for left rules:

```ocaml
and apply_ill_rule_internal rule_req ill_seq _notations =
    (* Validate that rule can be applied *)
    let can_apply, error_msg = Ill_rule_request.can_apply_rule rule_req.rule ill_seq in
    if not can_apply then
        raise (ILL_Rule_Application_Exception (true, error_msg));
    
    (* Apply the rule based on type *)
    match rule_req.rule with
    | ILL_Axiom -> apply_axiom_rule ill_seq
    | ILL_One -> apply_one_rule ill_seq
    | ILL_Top -> apply_top_rule ill_seq
    | ILL_Tensor -> apply_tensor_rule rule_req ill_seq
    | ILL_Tensor_left -> apply_tensor_left_rule rule_req ill_seq  (* NEW: pass rule_req *)
    | ILL_Plus_left -> apply_plus_left_rule ill_seq
    | ILL_Plus_right -> apply_plus_right_rule ill_seq
    | ILL_Lollipop -> apply_lollipop_rule ill_seq
    | ILL_Lollipop_left -> apply_lollipop_left_rule rule_req ill_seq  (* NEW: pass rule_req *)
```

### 4. Position-Aware Left Rule Implementation

**Enhance left rule implementations** to use specific formula positions:

```ocaml
(* Apply ILL tensor left rule at specific position *)
and apply_tensor_left_rule rule_req ill_seq =
    validate_single_conclusion ill_seq;
    
    match rule_req.formula_position with
    | Some pos when pos < List.length ill_seq.context ->
        let context_as_array = Array.of_list ill_seq.context in
        (match context_as_array.(pos) with
         | Tensor (a, b) ->
             (* Replace the tensor at position pos with its components *)
             context_as_array.(pos) <- a;
             let new_context = Array.to_list context_as_array @ [b] in
             let premise = { context = new_context; goal = ill_seq.goal } in
             
             validate_ill_sequent_constraints premise;
             let subproof = ILL_Hypothesis_proof premise in
             ILL_Tensor_left_proof (ill_seq.context, a, b, subproof)
         | _ ->
             raise (ILL_Rule_Application_Exception (true, 
                 "Position does not contain a tensor formula")))
    | _ ->
        (* Fallback to finding first tensor (current behavior) *)
        apply_tensor_left_rule_original ill_seq

(* Apply ILL lollipop left rule at specific position *)  
and apply_lollipop_left_rule rule_req ill_seq =
    validate_single_conclusion ill_seq;
    
    match rule_req.formula_position with
    | Some pos when pos < List.length ill_seq.context ->
        let context_list = ill_seq.context in
        let (before, at_pos, after) = split_list_at_position context_list pos in
        (match at_pos with
         | Lollipop (a, b) ->
             let remaining_context = before @ after in
             let premise1 = { context = remaining_context; goal = a } in
             let premise2 = { context = b :: remaining_context; goal = ill_seq.goal } in
             
             validate_ill_sequent_constraints premise1;
             validate_ill_sequent_constraints premise2;
             
             let subproof1 = ILL_Hypothesis_proof premise1 in
             let subproof2 = ILL_Hypothesis_proof premise2 in
             ILL_Lollipop_left_proof (ill_seq.context, a, b, subproof1, subproof2)
         | _ ->
             raise (ILL_Rule_Application_Exception (true, 
                 "Position does not contain a lollipop formula")))
    | _ ->
        (* Fallback to finding first lollipop (current behavior) *)
        apply_lollipop_left_rule_original ill_seq

(* Helper function to split list at specific position *)
and split_list_at_position list pos =
    let rec split acc n = function
        | [] -> (List.rev acc, None, [])
        | h :: t when n = 0 -> (List.rev acc, Some h, t)
        | h :: t -> split (h :: acc) (n - 1) t
    in
    match split [] pos list with
    | (before, Some at_pos, after) -> (before, at_pos, after)
    | (before, None, after) -> (before, failwith "Position out of bounds", after)
```

### 5. Enhanced JSON Parsing

**Modify `ill_rule_request.ml:226-251`** to handle the new `sequentSide` field:

```ocaml
let from_json json =
    try
        let rule = rule_from_json json in
        let formula_position = (* existing parsing logic *) in
        let side = (* existing parsing logic *) in
        
        (* NEW: Parse sequentSide field for better rule inference *)
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
            context_split = None;
            sequent_side = sequent_side;  (* NEW field *)
        }
```

## Implementation Phases

### Phase 1: Core Rule Inference (High Priority)
1. **Implement `infer_rule_from_side_and_formula()`** in `ill_rule_request.ml`
2. **Modify `apply_rule_with_exceptions()`** to use sequent side information
3. **Test basic left/right rule detection**

### Phase 2: Position-Aware Left Rules (Medium Priority)
1. **Enhance `apply_tensor_left_rule()`** to use specific positions
2. **Enhance `apply_lollipop_left_rule()`** to use specific positions  
3. **Add helper functions** for list manipulation

### Phase 3: Improved Error Handling (Low Priority)
1. **Add validation** for sequent side values
2. **Improve error messages** for invalid rule applications
3. **Add logging** for rule inference decisions

### Phase 4: Optimization (Future)
1. **Cache rule inference** results for performance
2. **Optimize position-based** list operations
3. **Add rule suggestion** API for better UX

## Backward Compatibility

### Existing LL Support
- **All LL functionality** remains unchanged - routing happens in `main.ml:129-140`
- **No changes to** `apply_rule.ml` or `rule_request.ml`
- **ILL mode is opt-in** via `intuitionisticMode` parameter

### Fallback Behavior
- **If `sequentSide` missing**: Fall back to current rule inference logic
- **If position out of bounds**: Use existing "find first" behavior
- **Unknown rules**: Return appropriate error messages

## Expected Outcome

After implementation:

1. **Frontend sends** `sequentSide: "left"/"right"` in rule requests
2. **Backend intelligently infers** whether to apply left or right rules
3. **Position-specific rule application** works correctly for complex sequents
4. **Error messages** clearly indicate why rules can't be applied
5. **All existing functionality** continues working unchanged

## Code Structure Changes

### New Files: None Required
All changes can be made to existing files.

### Modified Files:
1. `ill_apply_rule.ml` - Enhanced rule application logic
2. `ill_rule_request.ml` - Rule inference and position handling
3. (Optional) `ill_sequent.ml` - Helper functions if needed

### JSON Interface Extension:
```json
{
  "ruleRequest": {
    "rule": "tensor_left",
    "formulaPosition": 2,
    "sequentSide": "left"  // NEW field
  },
  "sequent": { /* existing sequent structure */ },
  "intuitionisticMode": true
}
```

This plan ensures the backend can properly support the left/right distinction proposed in `FRONTEND_WIP.md` while maintaining full backward compatibility with existing functionality.