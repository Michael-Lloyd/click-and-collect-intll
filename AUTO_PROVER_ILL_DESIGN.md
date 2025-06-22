# ILL Auto-Prover Design Documentation

## Overview

The Intuitionistic Linear Logic (ILL) auto-prover is an automated theorem proving system that attempts to find proofs for sequents in ILL. This document describes its architecture, algorithms, and implementation details.

## Key Differences from Classical Linear Logic

ILL differs from classical Linear Logic in several important ways:

1. **Asymmetric Sequents**: ILL sequents have the form `Γ ⊢ A` where:
   - `Γ` is a list of formulas (the context/assumptions)
   - `A` is a single formula (the goal/conclusion)
   - Classical LL allows multiple conclusions: `Γ ⊢ Δ`

2. **Restricted Connectives**: ILL has fewer connectives than classical LL:
   - **Removed**: Par (⅋), Why-not (?)
   - **Retained**: Tensor (⊗), With (&), Plus (⊕), Lollipop (⊸), Of-course (!), One (1), Top (⊤)

3. **Simpler Proof Search**: The single-conclusion restriction makes proof search more directed and often more efficient.

## Architecture

### Frontend Components

1. **User Interface** (`static/js/ui/interaction.js`):
   - Double-click on turnstile (⊢) triggers auto-prove
   - Shows loading spinner during proof search
   - Displays found proof or indicates unprovability

2. **Request Flow**:
   ```javascript
   autoProveSequent($sequentTable) {
     // 1. Extract sequent data
     // 2. Send AJAX request to /auto_prove_sequent
     // 3. Handle response (proof/timeout/unprovable)
   }
   ```

### Backend Components

1. **Main Entry Point** (`main.ml`):
   - Routes `/auto_prove_sequent` requests based on `intuitionisticMode` flag
   - Calls `Ill_auto_prove_sequent.auto_prove_sequent` for ILL mode

2. **Auto Prover Module** (`ill_auto_prove_sequent.ml`):
   - Core proof search implementation
   - Configuration management
   - Result handling

## Proof Search Algorithm

### Overall Strategy

The ILL auto-prover uses a **goal-directed, depth-first proof search** with the following phases:

1. **Axiom Check**: First check if the sequent is immediately provable as an axiom
2. **Introduction Rules**: Apply right rules based on the goal formula structure
3. **Left Rules**: When goal is atomic, decompose context formulas
4. **Backtracking**: Try alternative rules/splits when a branch fails

### Search Configuration

```ocaml
type ill_prover_config = {
  max_depth: int;          (* Default: 50 *)
  timeout_ms: int;         (* Default: 5000ms *)
  enable_heuristics: bool; (* Default: true *)
}
```

### Result Types

```ocaml
type ill_proof_result =
  | ILL_Proof_Found of ill_proof     (* Success with proof tree *)
  | ILL_Not_Provable                 (* Exhausted all possibilities *)
  | ILL_Timeout                      (* Time limit exceeded *)
  | ILL_Depth_Exceeded               (* Depth limit exceeded *)
  | ILL_Search_Error of string       (* Error during search *)
```

## Rule Application Strategy

### 1. Axiom Rule
```
A ⊢ A  (when context = [A] and goal = A)
```
- Always checked first
- Immediate success if applicable

### 2. Right Rules (Goal-Directed)

Based on the goal formula type, apply the appropriate introduction rule:

#### One Rule (⊢ 1)
```
─────  (requires empty context)
⊢ 1
```

#### Top Rule (Γ ⊢ ⊤)
```
──────  (always succeeds)
Γ ⊢ ⊤
```

#### Tensor Rule (Γ,Δ ⊢ A⊗B)
```
Γ ⊢ A    Δ ⊢ B
───────────────
  Γ,Δ ⊢ A⊗B
```
- **Challenge**: Must try all possible ways to split context
- **Implementation**: Generates all context splits, tries each

#### With Rule (Γ ⊢ A&B)
```
Γ ⊢ A    Γ ⊢ B
───────────────
    Γ ⊢ A&B
```
- Both branches must succeed
- Context is duplicated for each branch

#### Plus Rules (Γ ⊢ A⊕B)
```
  Γ ⊢ A           Γ ⊢ B
─────────  or  ─────────
Γ ⊢ A⊕B        Γ ⊢ A⊕B
```
- Try left branch first, then right
- First success wins

#### Lollipop Rule (Γ ⊢ A⊸B)
```
Γ, A ⊢ B
─────────
Γ ⊢ A⊸B
```
- Add A to context, prove B

#### Promotion Rule (!Γ ⊢ !A)
```
!Γ ⊢ A
───────  (all context formulas must be exponential)
!Γ ⊢ !A
```

### 3. Left Rules (Context Decomposition)

When the goal is atomic, try decomposing context formulas:

#### Tensor Left (Γ,A⊗B,Δ ⊢ C)
```
Γ,A,B,Δ ⊢ C
─────────────
Γ,A⊗B,Δ ⊢ C
```

#### With Left (Γ,A&B,Δ ⊢ C)
```
Γ,A,Δ ⊢ C        Γ,B,Δ ⊢ C
──────────  or  ──────────
Γ,A&B,Δ ⊢ C     Γ,A&B,Δ ⊢ C
```

#### Plus Left (Γ,A⊕B,Δ ⊢ C)
```
Γ,A,Δ ⊢ C    Γ,B,Δ ⊢ C
────────────────────────
     Γ,A⊕B,Δ ⊢ C
```
- Both branches must succeed

#### Lollipop Left (Γ,A⊸B,Δ ⊢ C)
```
Γ ⊢ A    Δ,B ⊢ C
─────────────────
  Γ,A⊸B,Δ ⊢ C
```
- Must prove A from left context
- Must prove C with B added to right context

### 4. Exponential Rules

#### Weakening (Γ,!A,Δ ⊢ B)
```
  Γ,Δ ⊢ B
───────────
Γ,!A,Δ ⊢ B
```
- Remove !A from context

#### Dereliction (Γ,!A,Δ ⊢ B)
```
 Γ,A,Δ ⊢ B
───────────
Γ,!A,Δ ⊢ B
```
- Replace !A with A

#### Contraction (Γ,!A,Δ ⊢ B)
```
Γ,!A,!A,Δ ⊢ B
──────────────
  Γ,!A,Δ ⊢ B
```
- Currently only applies when duplicates already exist
- Future enhancement: could duplicate !A when needed

## Exchange Rule Handling

The ILL auto-prover now implements full exchange rule support, treating contexts as multisets rather than ordered lists. This is crucial for completeness since many proofs require rearranging context formulas.

### Implementation Approach

1. **Permutation Generation**: For rules that split the context (tensor, lollipop left), the prover generates all permutations of the context formulas before trying splits.

2. **Partition Generation**: The `generate_all_partitions` function:
   - Generates all permutations of the context
   - For each permutation, generates all possible ways to split it
   - Removes duplicate partitions (same formulas in each part)

### Context Splitting Algorithm

For tensor rule and lollipop left, all possible partitions are tried:

```ocaml
generate_all_partitions [A; B; C] =
  (* All permutations: [A;B;C], [A;C;B], [B;A;C], [B;C;A], [C;A;B], [C;B;A] *)
  (* Then all splits of each permutation *)
  [([], [A; B; C]);    ([A], [B; C]);      ([A; B], [C]);      ([A; B; C], []);
   ([], [A; C; B]);    ([A], [C; B]);      ([A; C], [B]);      ([A; C; B], []);
   ([], [B; A; C]);    ([B], [A; C]);      ([B; A], [C]);      ([B; A; C], []);
   ([], [B; C; A]);    ([B], [C; A]);      ([B; C], [A]);      ([B; C; A], []);
   ([], [C; A; B]);    ([C], [A; B]);      ([C; A], [B]);      ([C; A; B], []);
   ([], [C; B; A]);    ([C], [B; A]);      ([C; B], [A]);      ([C; B; A], [])]
  (* After removing duplicates *)
```

### Examples Where Exchange is Essential

1. **Tensor with reversed context**: `B, A ⊢ A ⊗ B`
   - Without exchange: Would fail as it tries `[B] ⊢ A` and `[A] ⊢ B`
   - With exchange: Succeeds by trying `[A] ⊢ A` and `[B] ⊢ B`

2. **Complex tensor**: `A, B, C ⊢ B ⊗ (A ⊗ C)`
   - Requires partitioning as `[B]` and `[A, C]`
   - Only possible by first permuting to `[B, A, C]`

3. **Lollipop left with reordering**: `D, A, B⊸C, E ⊢ (A⊗D⊗E)⊸C`
   - Requires grouping `[A, D, E]` together for the left premise
   - Achieved through appropriate permutation before splitting

### Performance Impact

- **Complexity**: For n formulas, generates n! permutations
- **Optimization**: Duplicate partitions are filtered out using string comparison
- **Trade-off**: Completeness vs. performance - necessary for correctness

## Search Optimizations

1. **Depth Limiting**: Prevents infinite loops in cyclic search spaces
2. **Timeout**: Ensures responsiveness (default 5 seconds)
3. **Deterministic Rules First**: Always try invertible rules before choices
4. **Heuristics**: Prefer smaller contexts when enabled

## Debugging Features

### Frontend Logging
- `[ILL Auto-Prover] Sending request to backend:` - Shows full request
- `[ILL Auto-Prover] Response received:` - Shows backend response
- `[ILL Auto-Prover] Request timed out after 30 seconds` - Timeout detection

### Backend Logging
- `[ILL Auto-Prover] ========== START AUTO PROVE REQUEST ==========`
- `[ILL Auto-Prover] Depth N: Searching proof for sequent:`
- `[ILL Auto-Prover] Trying introduction rules for goal type:`
- `[ILL Auto-Prover] Trying tensor rule for A ⊗ B`
- `[ILL Auto-Prover] Generating partitions for N formulas, M permutations`
- `[ILL Auto-Prover] Generated N unique partitions (with exchange)`
- `[ILL Auto-Prover] Tensor split N: left=..., right=...`
- `[ILL Auto-Prover] Trying lollipop left for A⊸B at position N`
- `[ILL Auto-Prover] Trying partition: Γ=..., Δ=...`
- `[ILL Auto-Prover] Axiom found: A ⊢ A`
- `[ILL Auto-Prover] PROOF FOUND!` / `NOT PROVABLE` / `TIMEOUT`

## Limitations and Future Enhancements

### Current Limitations
1. **No Contraction Generation**: Cannot duplicate !A formulas on demand
2. **Basic Heuristics**: Simple context size preference
3. **No Proof Optimization**: Returns first proof found, not necessarily smallest
4. **Fixed Strategy**: No user control over search strategy

### Potential Enhancements
1. **Iterative Deepening**: Start with small depth, increase gradually
2. **Parallel Search**: Try multiple branches concurrently
3. **Learning**: Remember successful patterns for similar sequents
4. **Proof Simplification**: Post-process to remove redundant steps
5. **Better Heuristics**: Consider formula structure, not just context size

## Error Handling

1. **Malformed Sequents**: Checked at parsing stage
2. **Stack Overflow**: Caught and reported as depth exceeded
3. **Timeouts**: Both frontend (30s) and backend (5s) timeouts
4. **Invalid Rules**: Prevented by type system

## Performance Considerations

- **Exponential Complexity**: Context splitting for tensor creates 2^n branches
- **Memory Usage**: Proof trees stored in memory during search
- **Typical Performance**: Simple sequents prove in milliseconds, complex ones may timeout

## Integration Points

1. **Frontend**: `autoProveSequent()` in `interaction.js`
2. **Backend**: `auto_prove_sequent` in `ill_auto_prove_sequent.ml`
3. **Routing**: `/auto_prove_sequent` endpoint in `main.ml`
4. **Data Format**: JSON with compressed field names

This design provides a solid foundation for automated theorem proving in ILL while maintaining reasonable performance for typical use cases.