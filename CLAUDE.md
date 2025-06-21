# Overview

This repository contains the code for a linear logic interactive theorem prover. 

Recently an extension has started being worked on, extending the app from just linear logic, 
to intuitionistic linear logic (ILL). 

All of the frontend javascript can be found in `static/js/` and the backend can be found in the
working directory as OCaml code. 

On the frontend, a toggle slider enables ILL logic (as `intuitionisticMode=1`). 

The implementation of ILL should remain mostly separate from the original LL implementation. 

# ILL Rules 

The rules used in this ILL implementation are slightly altered to make rule application more
deterministic. You should follow these definitions closely. Below, things like `|-` for turnstile
are just ASCII forms, and you should convert them to symbols where relevant. 

## Axiom 

```

--------(ax)
A |- A 
```

## Left Tensor

```
Gamma, A, B |- C
-----------------(*_L)
Gamma, A*B |- C
```

## Right Tensor

```
Gamma |- A <gap> Delta |- B
----------------------------(*_R)
Gamma, Delta |- A * B 
```

## Left Lollipop 

```
Gamma |- A <gap> Delta, B |- C
-------------------------------(-o_L)
Gamma, A -o B, Delta |- C 
```

## Right Lollipop 

```
Gamma, A |- B 
-----------------(-o_R)
Gamma |- A -o B
```

## Left With 1

```
Gamma, A |- C
-----------------(&_L_1) 
Gamma, A&B |- C
```

## Left With 2

```
Gamma, B |- C
-----------------(&_L_2)
Gamma, A&B |- C 
```

## Right With 

```
Gamma |- A <gap> Gamma |- B
----------------------------(&_R)
Gamma |- A&B
```

## Left Additive Disjunction

```
Gamma, A |- C <gap> Gamma, B |- C
----------------------------------(+_L)
Gamma, A+B |- C
```

## Right Additive Disjunction 1

```
Gamma |- A
-------------(+_R_1)
Gamma |- A+B 
```

## Right Additive Disjunction 2

```
Gamma |- B
-------------(+_R_2)
Gamma |- A+B
```

## Cut rule 

```
Gamma |- B <gap> B, Delta |- C
-------------------------------(cut)
Gamma, Delta |- C
```

## Weakening 

```
Gamma |- B 
---------------(!w)
Gamma, !A |- B 
```

## Contraction 

```
Gamma, !A, !A |- B 
-------------------(!c)
Gamma, !A |- B
```

## Dereliction 

```
Gamma, A |- B
---------------(!d)
Gamma, !A |- B
```

## Promotion 

```
!Gamma |- A 
---------------(!p)
!Gamma |- !A 
```
