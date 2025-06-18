The following are required fixes to bugs, or additions of features that should be added. 

## 2. Conditional behaviour of dots/spaces and commas for ILL cut mode when right tensor is applicable

When in ILL mode, and when the right tensor is applicable, but cut mode is enabled, there are two
sets of dots that appear on the left side of the turnstile. For example, in the proof "A, B |- A*B"
there are two dots on the left of A, and two dots on the right of B. 

Additionally, the comma that separates A and B in that example has the problem where if you click on
it, it applies the tensor rule but a popup appears to enter a formula to apply the cut rule. 

The way you should handle this is, to check if cut mode is enabled before the comma and dots for 
ILL right tensor are set to be used for applying the ILL right tensor rule. In the case cut mode is 
enabled, do not use the comma or dots for right tensor rule, but instead have them used for cut
mode's splitting of Gamma and Delta. 

## 3. Highlighting of dots and commas cut rule application in cut mode 

When cut mode is enabled, hovering over the dots that appear beside contexts/formulae that appear in
cut mode should be highlighted the same way that clickable commas/spaces/dots are on the left side
of the turnstile when right tensor is applicable in ILL mode. 

## 4. When cut mode is enabled in ILL mode, dots should not appear on right side of turnstile 

When in ILL mode, and after enabling cut mode, there should not be dots on the right side of the
turnstile. These dots should only appear on the left side of the turnstile. 
