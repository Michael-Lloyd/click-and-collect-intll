# Work that's left over from last time 

## Autoprover update for Left 1 and Right 1 

The autoprover needs to be updated so that it uses the left 1 and right 1 rules in its proof search.

## Left 0 rule 

I didn't implement this in the backend, but the left 0 rule needs to be implemented into the
backend for rare but possible cases where:

```
---------------(0_L)
Gamma, 0 |- A 
```

I presume this will also require some additions to the fronend 
