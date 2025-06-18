The following are required fixes to bugs, or additions of features that should be added. 

## 1. Clickable empty spaces for right tensor rule application in ILL mode should be dots instead 

When in ILL mode, and when the right tensor is applicable, the spaces that appear on the left and
right sides of the contexts/formulae on the left side of the turnstile, should appear as dots,
instead of empty spaces. 

For example in the proof "A, B |- A*B" there are empty spaces that appear on the left of A, and on
the right of B. These should instead appear as dots. 

Please note when the right tensor rule is NOT applicable, the dots should not appear. 


## 2. Conditional behaviour of dots/spaces and commas for ILL cut mode when right tensor is applicable

When in ILL mode, and when the right tensor is applicable, but cut mode is enabled, the following
should apply:

Assuming TODO 1 is implemented, then there should be dots that appear on the left and right of the 
contexts/formulae on the left side of the turnstile (when right tensor is applicable in ILL mode).

Since cut mode is enabled, clicking on any of the dots or the commas should not split the context
and apply the right tensor rule, but instead be used to apply the cut rule. 

## 3. Highlighting of dots and commas cut rule application in cut mode 

When cut mode is enabled, hovering over the dots that appear beside contexts/formulae that appear in
cut mode should be highlighted the same way that clickable commas/spaces/dots are on the left side
of the turnstile when right tensor is applicable in ILL mode. 

## 4. When cut mode is enabled in ILL mode, dots should not appear on right side of turnstile 

When in ILL mode, and after enabling cut mode, there should not be dots on the right side of the
turnstile. These dots should only appear on the left side of the turnstile. 
