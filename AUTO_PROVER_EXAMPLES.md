
## Cases where Auto Prover fails in ILL mode: 

### (A-oB)*C |- A-o(B*C)

Entered proof: 

```
(A⊸B)⊗C ⊢ A⊸(B⊗C) 
```

Result:

Proof disappears

### !(A&B) |- !A*!B: 

Entered proof: 

```
!(A&B) ⊢ !A⊗!B 
```

Result: 

Proof disappears 
