# Examples to test ILL Auto-Prover

## Multiplicatives  

A⊗B ⊢ B⊗A 
Status=Pass

(A⊗B)⊗C ⊢ A⊗(B⊗C)
Status=Pass

A⊸B⊸C ⊢ A⊗B⊸C 
Status=Pass

A⊗(B⊗C) ⊢ (A⊗B)⊗C
Status=Pass

A⊗B⊸C ⊢ A⊸B⊸C 
Status=Pass

A ⊢ A⊗1
Status=Pass

1⊸A ⊢ A 
Status=Pass

A⊗1 ⊢ A
Status=Fail

A ⊢ 1⊸A 
Status=Fail

(A⊸B)⊗C ⊢ A⊸(B⊗C)
Status=Pass

A⊸A
Status=Pass

A⊸B, B⊸C ⊢ A⊸C
Status=Pass

A⊗(A⊸B) ⊢ B
Status=Pass

## Additives 

A&B ⊢ B&A
Status=Pass

A⊕B ⊢ B⊕A 
Status=Pass

(A&B)&C ⊢ A&(B&C) 
Status=Pass

A⊕(B⊕C) ⊢ (A⊕B)⊕C
Status=Pass

A&(B&C) ⊢ (A&B)&C
Status=Pass

(A⊕B)⊕C ⊢ A⊕(B⊕C)
Status=Pass

A ⊢ A&⊤
Status=Pass

A⊕0 ⊢ A
Status=Fail

A&⊤ ⊢ A
Status=Pass

A ⊢ A⊕0 
Status=Fail

A ⊢ A&A
Status=Pass

A⊕A ⊢ A
Status=Pass

A&B ⊢ A
Status=Pass

A ⊢ A⊕B
Status=Pass

A ⊢ ⊤
Status=Pass

0 ⊢ A
Status=Fail

A⊕(B&C) ⊢ (A⊕B)&(A⊕C)
Status=Pass

(A&B)⊕(A&C) ⊢ A&(B⊕C)
Status=Pass

