# ILL Backend Auto-Prover Implementation Plan

## Overview

This document outlines the implementation plan for completing the Intuitionistic Linear Logic (ILL) automated theorem prover backend. The current implementation in `ill_auto_prove_sequent.ml` and `ill_auto_reverse_sequent.ml` is mostly stubbed out and needs to be completed to provide automated proof search for ILL sequents.

## Current State Analysis

### Completed Components
1. **ILL Data Structures** (`ill_sequent.ml`, `ill_proof.ml`):
   - Complete ILL formula and sequent definitions
   - ILL proof tree representation with all rule constructors
   - JSON serialization and validation

2. **ILL Rule Application** (`ill_apply_rule.ml`, `ill_rule_request.ml`):
   - Comprehensive rule application logic for all ILL rules
   - Rule validation and constraint checking
   - Context splitting for tensor rules
   - Position-based rule application

3. **Test Infrastructure**:
   - Extensive test suite in `test/ill_tests/` covering all ILL rules
   - Test cases for axioms, connectives, and invalid applications

### Missing/Incomplete Components
1. **Auto-Prove Engine** (`ill_auto_prove_sequent.ml`):
   - Proof search algorithm is stubbed (returns `ILL_Timeout`)
   - Missing backward chaining logic
   - Missing heuristics and optimization

2. **Auto-Reverse Engine** (`ill_auto_reverse_sequent.ml`):
   - Rule inference logic incomplete
   - Missing exhaustive rule application

3. **Context Splitting Strategy**:
   - Tensor rule requires smart context splitting for multiple possibilities
   - Currently only implements trivial splits

## Implementation Strategy

### Phase 1: Core Proof Search Algorithm

#### 1.1 Goal-Directed Search Foundation
ILL is well-suited for goal-directed proof search due to its asymmetric sequents (Γ ⊢ A). The algorithm should work backwards from the goal:

```ocaml
(* Main proof search with backtracking *)
let rec prove_ill_sequent_internal ill_seq config =
    (* Check termination conditions *)
    if is_axiom ill_seq then
        ILL_Proof_Found (construct_axiom_proof ill_seq)
    else if depth_exceeded config then
        ILL_Depth_Exceeded
    else if timeout_exceeded config then
        ILL_Timeout
    else
        (* Try applicable rules in priority order *)
        try_all_applicable_rules ill_seq config
```

#### 1.2 Rule Priority System
Based on the ILL rules from CLAUDE.md, implement this rule priority:

1. **Deterministic/Invertible Rules (High Priority)**:
   - Top introduction: `Γ ⊢ ⊤` (always succeeds)
   - Lollipop introduction: `Γ ⊢ A⊸B → Γ,A ⊢ B` (deterministic)
   - With right: `Γ ⊢ A&B → Γ ⊢ A ∧ Γ ⊢ B` (deterministic)
   - One introduction: `⊢ 1` (only if context empty)

2. **Non-deterministic Rules (Medium Priority)**:
   - Plus right: `Γ ⊢ A⊕B → Γ ⊢ A | Γ ⊢ B` (choice between left/right)
   - Left rules when multiple options exist

3. **Expensive Rules (Lower Priority)**:
   - Tensor right: `Γ,Δ ⊢ A⊗B → Γ ⊢ A ∧ Δ ⊢ B` (requires context splitting)

#### 1.3 Axiom Recognition
```ocaml
let is_axiom ill_seq =
    match ill_seq.context, ill_seq.goal with
    | [Litt a], Litt b when a = b -> true
    | _ -> false
```

### Phase 2: Context Splitting for Tensor Rules

#### 2.1 The Context Splitting Challenge
For tensor right rule `Γ,Δ ⊢ A⊗B`, we need to split context `Γ,Δ` into `Γ` and `Δ` such that:
- `Γ ⊢ A` is provable
- `Δ ⊢ B` is provable

#### 2.2 Splitting Strategy Implementation
```ocaml
(* Generate all possible context splits *)
let generate_all_context_splits context =
    let n = List.length context in
    let rec generate_splits acc i =
        if i > n then acc
        else
            let left_ctx = take i context in
            let right_ctx = drop i context in
            (left_ctx, right_ctx) :: generate_splits acc (i + 1)
    in
    generate_splits [] 0

(* Try tensor rule with intelligent splitting *)
let try_tensor_rule ill_seq a b config depth start_time =
    let splits = generate_all_context_splits ill_seq.context in
    let splits_sorted = sort_splits_by_heuristic splits a b in
    try_splits_until_success splits_sorted a b config depth start_time
```

#### 2.3 Context Splitting Heuristics
- **Resource-based**: Assign formulas to subgoals based on what's needed
- **Size-based**: Try balanced splits first
- **Type-based**: Group similar formulas together

### Phase 3: Left Rules and Focusing

#### 3.1 Left Rule Application
When goal is atomic or no right rules apply, try left rules:

```ocaml
let try_left_rules ill_seq config depth start_time =
    let applicable_left_rules = find_applicable_left_rules ill_seq.context in
    try_rules_in_sequence applicable_left_rules ill_seq config depth start_time

let find_applicable_left_rules context =
    List.fold_left (fun acc (i, formula) ->
        match formula with
        | Tensor (a, b) -> (ILL_Tensor_left, i, a, b) :: acc
        | With (a, b) -> (ILL_With_left_1, i, a, b) :: (ILL_With_left_2, i, a, b) :: acc
        | Plus (a, b) -> (ILL_Plus_left, i, a, b) :: acc
        | Lollipop (a, b) -> (ILL_Lollipop_left, i, a, b) :: acc
        | _ -> acc
    ) [] (List.mapi (fun i f -> (i, f)) context)
```

#### 3.2 Non-deterministic Choice Handling
For rules with choices (With_left_1 vs With_left_2, Plus_right_1 vs Plus_right_2):

```ocaml
let try_with_left_rules context pos a b config depth start_time =
    (* Try with_left_1 first *)
    match try_with_left_1 context pos a config depth start_time with
    | ILL_Proof_Found proof -> ILL_Proof_Found proof
    | _ -> try_with_left_2 context pos b config depth start_time
```

### Phase 4: Optimizations and Heuristics

#### 4.1 Proof Search Optimizations
1. **Memoization**: Cache failed proof attempts
2. **Iterative Deepening**: Start with small depth, increase gradually
3. **Resource Counting**: Fail early if resources don't match

#### 4.2 Smart Heuristics
```ocaml
let compute_heuristic_score ill_seq config =
    let context_size = List.length ill_seq.context in
    let goal_complexity = formula_complexity ill_seq.goal in
    let resource_balance = compute_resource_balance ill_seq in
    context_size + goal_complexity + resource_balance
```

#### 4.3 Cut-off Strategies
- **Depth limit**: Prevent infinite recursion
- **Time limit**: Respect timeout constraints
- **Resource limit**: Prevent exponential explosion

### Phase 5: Auto-Reverse Implementation

#### 5.1 Exhaustive Invertible Rule Application
Auto-reverse should apply all invertible rules until a fixpoint:

```ocaml
let rec apply_auto_reverse_exhaustive proof config =
    match try_apply_invertible_rule proof config with
    | Some (new_proof, rule_name) ->
        (* Continue applying rules *)
        apply_auto_reverse_exhaustive new_proof config
    | None ->
        (* No more invertible rules *)
        proof
```

#### 5.2 Invertible Rules in ILL
- **Top**: Always invertible when goal is ⊤
- **Lollipop**: Always invertible when goal is A⊸B
- **Tensor_left**: Invertible when A⊗B in context
- **Plus_left**: Invertible when A⊕B in context

### Phase 6: Integration and Testing

#### 6.1 API Integration
Update the JSON API to properly handle:
- Configuration parameters (timeouts, depth limits)
- Progress reporting for long-running proofs
- Detailed error messages for failed proofs

#### 6.2 Performance Testing
- Benchmark against existing LL auto-prover
- Test on complex ILL theorems
- Measure timeout behavior and memory usage

## Implementation Order

### Week 1: Core Search Algorithm
- [ ] Implement basic goal-directed search loop
- [ ] Add axiom detection and simple rules (Top, One, Lollipop)
- [ ] Basic depth and timeout checking

### Week 2: Context Splitting
- [ ] Implement context splitting generator
- [ ] Add tensor rule with splitting
- [ ] Basic splitting heuristics

### Week 3: Left Rules and Choices
- [ ] Implement all left rules
- [ ] Add choice handling for With_left and Plus_right
- [ ] Non-deterministic search with backtracking

### Week 4: Optimization and Integration
- [ ] Add heuristics and optimizations
- [ ] Complete auto-reverse implementation
- [ ] Integration testing and performance tuning

## Testing Strategy

### Unit Tests
- Test each rule implementation individually
- Test context splitting correctness
- Test termination conditions

### Integration Tests
- Test complete proof search on known theorems
- Test timeout and depth limit behavior
- Test against existing LL prover for compatibility

### Performance Tests
- Benchmark proof search times
- Memory usage profiling
- Scalability testing with complex formulas

## Risk Mitigation

### Complexity Risks
- **Context splitting explosion**: Use heuristics and early pruning
- **Search space size**: Implement iterative deepening and memoization
- **Non-termination**: Strict depth and time limits

### Compatibility Risks
- **Frontend integration**: Maintain existing JSON API
- **LL compatibility**: Ensure ILL proofs work with existing infrastructure
- **Performance regression**: Benchmark against current implementation

## Success Metrics

1. **Completeness**: Auto-prover finds proofs for all provable ILL sequents (within reasonable limits)
2. **Soundness**: All generated proofs are valid ILL proofs
3. **Performance**: Proof search completes within reasonable time for typical problems
4. **Integration**: Seamless operation with existing frontend and test suite

## Conclusion

This implementation plan provides a systematic approach to completing the ILL auto-prover. The goal-directed nature of ILL makes it well-suited for automated proof search, and the modular design allows for incremental implementation and testing. The key challenges are managing the non-deterministic context splitting for tensor rules and ensuring good performance through heuristics and optimizations.