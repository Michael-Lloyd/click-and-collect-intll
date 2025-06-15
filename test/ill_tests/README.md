# Input format 

Inputs should be identical to what the app frontend sends to the server backend for parsing proofs 
and applying rules. 

# Required tests 

Each test should verify that the ILL proof rules are correctly implemented and that the system properly handles both valid and invalid rule applications. Tests should be provided as JSON objects following the same format as the existing linear logic tests.

## Axiom tests 

Tests for the axiom rule: `A ⊢ A`

**Valid cases:**
- Simple atomic propositions: `A ⊢ A`, `B ⊢ B`
- Complex formulas used axiomatically: `(A ⊗ B) ⊢ (A ⊗ B)`, `(A ⊸ B) ⊢ (A ⊸ B)`

**Invalid cases:**
- Different formulas: `A ⊢ B`
- Multiple assumptions: `A, B ⊢ A`
- Multiple conclusions: `A ⊢ A, B` (ILL allows only single conclusion)

## One tests 

Tests for the multiplicative unit (1) handling.

**Valid cases:**
- Proving unit: `⊢ 1`
- Unit in context: `1, A ⊢ B` (where A ⊢ B is provable)

**Invalid cases:**
- Unit with premises: `A ⊢ 1` (where A ≠ 1)

## Top tests 

Tests for the additive unit (⊤) handling.

**Valid cases:**
- Proving top: `Γ ⊢ ⊤` (always provable from any context)
- Top in context: `⊤, A ⊢ B` (⊤ can be ignored)

**Invalid cases:**
- None (⊤ is always provable)

## Left tensor tests 

Tests for the left tensor rule: `Γ, A, B ⊢ C / Γ, A ⊗ B ⊢ C`

**Valid cases:**
- Simple decomposition: `A, B ⊢ C` becomes `A ⊗ B ⊢ C`
- With additional context: `Γ, A, B ⊢ C` becomes `Γ, A ⊗ B ⊢ C`
- Nested tensors: `A, B, C ⊢ D` becomes `A ⊗ B, C ⊢ D` becomes `(A ⊗ B) ⊗ C ⊢ D`

**Invalid cases:**
- Wrong decomposition: `A ⊗ B ⊢ C` where `A, B ⊢ C` is not provable
- Missing components: `A ⊢ C` cannot be derived from `A ⊗ B ⊢ C`

## Right tensor tests 

Tests for the right tensor rule: `Γ ⊢ A, Δ ⊢ B / Γ, Δ ⊢ A ⊗ B`

**Valid cases:**
- Simple combination: `Γ ⊢ A` and `Δ ⊢ B` gives `Γ, Δ ⊢ A ⊗ B`
- Empty contexts: `⊢ A` and `⊢ B` gives `⊢ A ⊗ B`
- Overlapping contexts: proper resource management

**Invalid cases:**
- Resource conflicts: attempting to use the same resource twice
- Unprovable subgoals: `Γ ⊢ A` or `Δ ⊢ B` not provable

## Left lollipop tests 

Tests for the left lollipop rule: `Γ ⊢ A, Δ, B ⊢ C / Γ, A ⊸ B, Δ ⊢ C`

**Valid cases:**
- Simple modus ponens: `⊢ A` and `B ⊢ C` gives `A ⊸ B ⊢ C`
- With contexts: `Γ ⊢ A` and `Δ, B ⊢ C` gives `Γ, A ⊸ B, Δ ⊢ C`
- Chained lollipops: `A ⊸ B, B ⊸ C ⊢ A ⊸ C`

**Invalid cases:**
- Wrong premise: `Γ ⊢ A'` where A' ≠ A
- Unprovable subgoals: either premise not provable

## Right lollipop tests 

Tests for the right lollipop rule: `Γ, A ⊢ B / Γ ⊢ A ⊸ B`

**Valid cases:**
- Simple implication: `A ⊢ B` gives `⊢ A ⊸ B`
- With context: `Γ, A ⊢ B` gives `Γ ⊢ A ⊸ B`
- Nested implications: `A, B ⊢ C` gives `A ⊢ B ⊸ C` gives `⊢ A ⊸ (B ⊸ C)`

**Invalid cases:**
- Unprovable premise: `Γ, A ⊢ B` not provable
- Resource conflicts: attempting to use context resources improperly

## Left with 1 tests 

Tests for the left with rule 1: `Γ, A ⊢ C / Γ, A & B ⊢ C`

**Valid cases:**
- First projection: `A ⊢ C` gives `A & B ⊢ C`
- With context: `Γ, A ⊢ C` gives `Γ, A & B ⊢ C`
- Nested withs: `A ⊢ C` gives `A & B ⊢ C` gives `(A & B) & D ⊢ C`

**Invalid cases:**
- Wrong projection: `B ⊢ C` does not give `A & B ⊢ C` via this rule
- Unprovable premise: `Γ, A ⊢ C` not provable

## Left with 2 tests 

Tests for the left with rule 2: `Γ, B ⊢ C / Γ, A & B ⊢ C`

**Valid cases:**
- Second projection: `B ⊢ C` gives `A & B ⊢ C`
- With context: `Γ, B ⊢ C` gives `Γ, A & B ⊢ C`
- Choice of projection: same premise `A & B ⊢ C` can be proven via either rule

**Invalid cases:**
- Wrong projection: `A ⊢ C` does not give `A & B ⊢ C` via this rule
- Unprovable premise: `Γ, B ⊢ C` not provable

## Right with tests 

Tests for the right with rule: `Γ ⊢ A, Γ ⊢ B / Γ ⊢ A & B`

**Valid cases:**
- Both conjuncts: `Γ ⊢ A` and `Γ ⊢ B` gives `Γ ⊢ A & B`
- Empty context: `⊢ A` and `⊢ B` gives `⊢ A & B`
- Identical context: same assumptions used for both subgoals

**Invalid cases:**
- Different contexts: `Γ ⊢ A` and `Δ ⊢ B` where Γ ≠ Δ
- Unprovable subgoals: either `Γ ⊢ A` or `Γ ⊢ B` not provable
- Resource conflicts: attempting to use linear resources twice

## Left additive disjunction tests 

Tests for the left plus rule: `Γ, A ⊢ C, Γ, B ⊢ C / Γ, A ⊕ B ⊢ C`

**Valid cases:**
- Both cases: `Γ, A ⊢ C` and `Γ, B ⊢ C` gives `Γ, A ⊕ B ⊢ C`
- Case analysis: handling both alternatives
- Nested plus: `A ⊕ B, C ⊢ D` requires `A, C ⊢ D` and `B, C ⊢ D`

**Invalid cases:**
- Only one case: `Γ, A ⊢ C` alone cannot prove `Γ, A ⊕ B ⊢ C`
- Unprovable cases: either branch not provable
- Different contexts: `Γ, A ⊢ C` and `Δ, B ⊢ C` where Γ ≠ Δ

## Right additive disjunction 1 tests 

Tests for the right plus rule 1: `Γ ⊢ A / Γ ⊢ A ⊕ B`

**Valid cases:**
- Left injection: `Γ ⊢ A` gives `Γ ⊢ A ⊕ B`
- Choice of alternative: proving first disjunct
- With context: any context that proves A can prove A ⊕ B

**Invalid cases:**
- Wrong alternative: `Γ ⊢ B` does not give `Γ ⊢ A ⊕ B` via this rule
- Unprovable premise: `Γ ⊢ A` not provable

## Right additive disjunction 2 tests 

Tests for the right plus rule 2: `Γ ⊢ B / Γ ⊢ A ⊕ B`

**Valid cases:**
- Right injection: `Γ ⊢ B` gives `Γ ⊢ A ⊕ B`
- Choice of alternative: proving second disjunct
- With context: any context that proves B can prove A ⊕ B

**Invalid cases:**
- Wrong alternative: `Γ ⊢ A` does not give `Γ ⊢ A ⊕ B` via this rule
- Unprovable premise: `Γ ⊢ B` not provable

## Format notes

Each test case should be a JSON object with:
- `"intuitionisticMode": 1` to enable ILL mode
- `"sequent"` field containing the sequent string (e.g., "A ⊢ B")
- `"rule"` field specifying the rule name (e.g., "axiom", "tensor_left", "lollipop_right")
- `"expected"` field indicating whether the test should pass (true) or fail (false)
- Optional `"description"` field explaining the test case

Example:
```json
{
  "intuitionisticMode": 1,
  "sequent": "A ⊢ A",
  "rule": "axiom",
  "expected": true,
  "description": "Basic axiom rule with atomic proposition"
}
``` 
