// INTUITIONISTIC LINEAR LOGIC MODE
// ILL implementation extending the abstract rule engine
// Contains all ILL-specific rule logic, symbols, and context splitting behavior

/**
 * Intuitionistic Linear Logic Rule Engine
 * Implements ILL rules with directional restrictions and context splitting
 */
class ILLRuleEngine extends RuleEngine {
    constructor() {
        super();
        this.ruleSymbols = ILL_RULES;
        this.modeName = 'intuitionistic';
    }

    /**
     * Get applicable rules for a formula in ILL mode
     * @param {Object} formulaAsJson - Formula data structure
     * @param {Object} options - Display and interaction options
     * @param {boolean} isLeftSide - Whether formula is on left side of turnstile
     * @param {jQuery} $li - List item element containing the formula
     * @return {Array} Array of rule event configurations
     */
    getRules(formulaAsJson, options, isLeftSide = false, $li = null) {
        if (!options.withInteraction && !options.proofTransformation?.value) {
            return [];
        }

        if (options.withInteraction) {
            return this.getInteractiveRules(formulaAsJson, isLeftSide, $li);
        } else if (options.proofTransformation?.value) {
            return this.getTransformationRules(formulaAsJson);
        }

        return [];
    }

    /**
     * Get interactive rules for ILL mode with directional restrictions
     * @param {Object} formulaAsJson - Formula data structure
     * @param {boolean} isLeftSide - Whether formula is on left side
     * @param {jQuery} $li - List item element (for context checking)
     * @return {Array} Array of rule event configurations
     */
    getInteractiveRules(formulaAsJson, isLeftSide, $li) {
        switch (formulaAsJson.type) {
            case 'litt':
            case 'dual':
                // ILL axiom rule with applicability checking
                return [{'element': 'main-formula', 'onclick': [{'rule': 'ill_axiom', 'needPosition': false}]}];

            case 'tensor':
                if (isLeftSide) {
                    // ILL: Left side tensor elimination
                    return [{'element': 'main-formula', 'onclick': [{'rule': 'ill_tensor_left', 'needPosition': true}]}];
                } else {
                    // ILL: Right side tensor introduction
                    return [{'element': 'main-formula', 'onclick': [{'rule': 'ill_tensor_right', 'needPosition': true}]}];
                }

            case 'par':
                // Par is only available in classical LL, not in ILL
                return [];
                
            case 'with':
                if (isLeftSide) {
                    // ILL: Left side with elimination (choose left or right sub-formula)
                    return [
                        {'element': 'left-formula', 'onclick': [{'rule': 'ill_with_left_1', 'needPosition': true}]},
                        {'element': 'right-formula', 'onclick': [{'rule': 'ill_with_left_2', 'needPosition': true}]}
                    ];
                } else {
                    // ILL: Right side with introduction
                    return [{'element': 'main-formula', 'onclick': [{'rule': 'ill_with_right', 'needPosition': true}]}];
                }

            case 'plus':
                if (isLeftSide) {
                    // ILL: Left side plus elimination
                    return [{'element': 'main-formula', 'onclick': [{'rule': 'ill_plus_left', 'needPosition': true}]}];
                } else {
                    // ILL: Right side plus introduction (choose left or right sub-formula)
                    return [
                        {'element': 'left-formula', 'onclick': [{'rule': 'ill_plus_right_1', 'needPosition': true}]},
                        {'element': 'right-formula', 'onclick': [{'rule': 'ill_plus_right_2', 'needPosition': true}]}
                    ];
                }

            case 'lollipop':
                if (isLeftSide) {
                    // ILL: Left side lollipop elimination (modus ponens)
                    return [{'element': 'main-formula', 'onclick': [{'rule': 'ill_lollipop_left', 'needPosition': true}]}];
                } else {
                    // ILL: Right side lollipop introduction (implication introduction)
                    return [{'element': 'main-formula', 'onclick': [{'rule': 'ill_lollipop_right', 'needPosition': true}]}];
                }

            case 'one':
                if (isLeftSide) {
                    // ILL: Left side one elimination (1_L rule)
                    return [{'element': 'main-formula', 'onclick': [{'rule': 'ill_one_left', 'needPosition': true}]}];
                } else {
                    // In ILL mode, one right rule only applicable on right side with empty context
                    // For the one right rule, we need to check if the context is empty
                    if ($li) {
                        let $sequentDiv = $li.closest('div.sequent');
                        if ($sequentDiv.length > 0) {
                            // Check if there's a hyp list (left side of turnstile)
                            let $hypList = $sequentDiv.find('ul.hyp');
                            
                            // The key insight: if there's no hyp list at all, the context is empty!
                            if ($hypList.length === 0) {
                                // Double-check by looking at all UL elements
                                let allULs = $sequentDiv.find('ul');
                                let hasHypList = false;
                                allULs.each(function() {
                                    if ($(this).hasClass('hyp')) {
                                        hasHypList = true;
                                    }
                                });
                                
                                if (!hasHypList) {
                                    return [{'element': 'main-formula', 'onclick': [{'rule': 'ill_one_right', 'needPosition': false}]}];
                                }
                            } else {
                                // There is a hyp list, check if it has any formulas
                                let hypFormulas = $hypList.find('li').length;
                                if (hypFormulas === 0) {
                                    return [{'element': 'main-formula', 'onclick': [{'rule': 'ill_one_right', 'needPosition': false}]}];
                                }
                            }
                        }
                    }
                }
                return [];

            case 'zero':
                // Zero rule does not exist
                return [];

            case 'top':
                // In ILL mode, top rule is always applicable on right side
                if (!isLeftSide) {
                    return [{'element': 'main-formula', 'onclick': [{'rule': 'ill_' + formulaAsJson.type, 'needPosition': true}]}];
                }
                return [];

            case 'bottom':
                // Bottom rule in ILL
                return [{'element': 'main-formula', 'onclick': [{'rule': 'ill_' + formulaAsJson.type, 'needPosition': true}]}];

            case 'ofcourse':
                if (isLeftSide) {
                    // ILL: !A on left side - handle weakening, contraction, dereliction
                    console.log('[ILL-MODE] Setting up ofcourse rules for left side');
                    let rules = [
                        {
                            'element': 'primaryConnector', 'onclick': [
                                {'rule': 'ill_weakening', 'needPosition': true},
                                {'rule': 'ill_contraction', 'needPosition': true}
                            ]
                        },
                        {
                            'element': 'sub-formula', 'onclick': [
                                {'rule': 'ill_dereliction', 'needPosition': true},
                                {'rule': 'ill_contraction', 'needPosition': true}
                            ]
                        }
                    ];
                    console.log('[ILL-MODE] Returning rules for ofcourse:', rules);
                    return rules;
                } else {
                    // ILL: !A on right side - promotion rule
                    return [{'element': 'main-formula', 'onclick': [{'rule': 'ill_promotion', 'needPosition': true}]}];
                }

            case 'whynot':
                // ILL doesn't use whynot (?A) - only ofcourse (!A)
                return [];

            default:
                return [];
        }
    }

    /**
     * Get transformation rules for ILL mode
     * @param {Object} formulaAsJson - Formula data structure
     * @return {Array} Array of rule event configurations
     */
    getTransformationRules(formulaAsJson) {
        console.log('[ILL-MODE] Getting transformation rules for formula type:', formulaAsJson.type);
        switch (formulaAsJson.type) {
            case 'tensor':
                console.log('[ILL-MODE] Returning tensor transformation rule');
                return [{'element': 'main-formula', 'onclick': [{'rule': 'ill_tensor_right', 'needPosition': true, 'transformation': 'apply_reversible_first'}]}];
                
            case 'with':
                console.log('[ILL-MODE] Returning with transformation rule');
                return [{'element': 'main-formula', 'onclick': [{'rule': 'ill_with_right', 'needPosition': true, 'transformation': 'apply_reversible_first'}]}];

            case 'plus':
                console.log('[ILL-MODE] Returning plus transformation rules');
                return [
                    {'element': 'left-formula', 'onclick': [{'rule': 'ill_plus_right_1', 'needPosition': true, 'transformation': 'apply_reversible_first'}]},
                    {'element': 'right-formula', 'onclick': [{'rule': 'ill_plus_right_2', 'needPosition': true, 'transformation': 'apply_reversible_first'}]}
                ];

            case 'lollipop':
                console.log('[ILL-MODE] Returning lollipop transformation rule');
                return [{'element': 'main-formula', 'onclick': [{'rule': 'ill_lollipop_right', 'needPosition': true, 'transformation': 'apply_reversible_first'}]}];

            case 'top':
                console.log('[ILL-MODE] Returning top transformation rule');
                return [{'element': 'main-formula', 'onclick': [{'rule': 'ill_top', 'needPosition': true, 'transformation': 'apply_reversible_first'}]}];

            case 'ofcourse':
                console.log('[ILL-MODE] Returning ofcourse transformation rule');
                return [{'element': 'main-formula', 'onclick': [{'rule': 'ill_promotion', 'needPosition': true, 'transformation': 'apply_reversible_first'}]}];

            default:
                console.log('[ILL-MODE] No transformation rules available for formula type:', formulaAsJson.type);
                return [];
        }
    }

    /**
     * Check if a rule can be applied to the given sequent in ILL mode
     * @param {Object} ruleRequest - Rule application request
     * @param {Object} sequent - Sequent data structure
     * @return {boolean} True if rule is applicable
     */
    canApplyRule(ruleRequest, sequent) {
        if (!ruleRequest || !ruleRequest.rule) {
            return false;
        }

        // ILL rule validation with stricter constraints
        switch (ruleRequest.rule) {
            case 'ill_axiom':
                return this.canApplyAxiom(sequent);
            case 'ill_one_right':
                // One right rule requires empty context and single formula on right
                return sequent.hyp.length === 0 && sequent.cons.length === 1;
            case 'ill_top':
                return sequent.cons.length === 1;
            case 'ill_tensor_right':
                return this.canApplyTensorRight(sequent);
            case 'ill_with_right':
                return sequent.cons.length === 1;
            case 'ill_weakening':
                return this.canApplyWeakening(sequent, ruleRequest);
            case 'ill_contraction':
                return this.canApplyContraction(sequent, ruleRequest);
            case 'ill_dereliction':
                return this.canApplyDereliction(sequent, ruleRequest);
            case 'ill_promotion':
                return this.canApplyPromotion(sequent);
            default:
                return true; // Most other rules are context-dependent
        }
    }

    /**
     * Check if axiom rule can be applied in ILL mode
     * @param {Object} sequent - Sequent data structure
     * @return {boolean} True if axiom is applicable
     */
    canApplyAxiom(sequent) {
        // ILL axiom requires exactly one context formula and one conclusion
        if (!sequent.hyp || !sequent.cons || 
            sequent.hyp.length !== 1 || sequent.cons.length !== 1) {
            return false;
        }

        let contextFormula = sequent.hyp[0];
        let goalFormula = sequent.cons[0];

        return formulasMatch(contextFormula, goalFormula);
    }

    /**
     * Check if tensor right rule can be applied
     * @param {Object} sequent - Sequent data structure
     * @return {boolean} True if tensor right is applicable
     */
    canApplyTensorRight(sequent) {
        if (!sequent.cons || sequent.cons.length !== 1) {
            return false;
        }

        let goalFormula = sequent.cons[0];
        return goalFormula.type === 'tensor';
    }

    /**
     * Check if one right rule is applicable (requires empty context and goal 1)
     * @param {jQuery} $sequentTable - Sequent table element
     * @return {boolean} True if one right rule can be applied
     */
    isOneRightRuleApplicable($sequentTable) {
        let sequent = $sequentTable.data('sequent') || $sequentTable.data('sequentWithoutPermutation');
        
        if (!sequent || !sequent.hyp || !sequent.cons || sequent.cons.length !== 1) {
            return false;
        }

        // One right rule requires empty context and goal must be 1
        return sequent.hyp.length === 0;
    }

    /**
     * Check if axiom rule is applicable with specific clicked formula
     * @param {jQuery} $sequentTable - Sequent table element
     * @param {Object} clickedFormula - The formula being clicked
     * @param {boolean} isLeftSide - Whether clicked formula is on left side
     * @return {boolean} True if axiom rule can be applied
     */
    isAxiomRuleApplicable($sequentTable, clickedFormula, isLeftSide) {
        let sequent = $sequentTable.data('sequent') || $sequentTable.data('sequentWithoutPermutation');
        
        if (!sequent || !sequent.hyp || !sequent.cons || sequent.cons.length !== 1) {
            return false;
        }

        // Axiom rule requires exactly one context formula
        if (sequent.hyp.length !== 1) {
            return false;
        }

        let contextFormula = sequent.hyp[0];
        let goalFormula = sequent.cons[0];

        // Check if context formula matches goal formula
        return formulasMatch(contextFormula, goalFormula);
    }

    /**
     * Check if contraction rule is applicable for a !A formula
     * @param {jQuery} $li - List item element containing the formula
     * @param {Object} formulaAsJson - The !A formula being checked
     * @return {boolean} True if contraction rule can be applied
     */
    isContractionApplicable($li, formulaAsJson) {
        let $sequentTable = $li.closest('table');
        let sequent = $sequentTable.data('sequent') || $sequentTable.data('sequentWithoutPermutation');
        
        if (!sequent || !sequent.hyp || sequent.hyp.length < 2) {
            return false;
        }

        // Count how many formulas in the context match this !A formula
        let matchingCount = 0;
        for (let hypFormula of sequent.hyp) {
            if (formulasMatch(hypFormula, formulaAsJson)) {
                matchingCount++;
            }
        }

        // Contraction is applicable if there are at least 2 identical !A formulas
        return matchingCount >= 2;
    }

    /**
     * Check if weakening rule can be applied (!w rule)
     * @param {Object} sequent - Sequent data structure
     * @param {Object} ruleRequest - Rule application request
     * @return {boolean} True if weakening rule can be applied
     */
    canApplyWeakening(sequent, ruleRequest) {
        // Weakening is generally applicable when we have !A in context
        // The backend will handle the specific validation
        return sequent && sequent.hyp && sequent.hyp.length > 0;
    }

    /**
     * Check if contraction rule can be applied (!c rule)
     * @param {Object} sequent - Sequent data structure
     * @param {Object} ruleRequest - Rule application request
     * @return {boolean} True if contraction rule can be applied
     */
    canApplyContraction(sequent, ruleRequest) {
        // Contraction requires at least one !A formula in context
        // The backend will check for duplicates
        return sequent && sequent.hyp && sequent.hyp.length > 0;
    }

    /**
     * Check if dereliction rule can be applied (!d rule)
     * @param {Object} sequent - Sequent data structure
     * @param {Object} ruleRequest - Rule application request
     * @return {boolean} True if dereliction rule can be applied
     */
    canApplyDereliction(sequent, ruleRequest) {
        // Dereliction is applicable when we have !A in context
        return sequent && sequent.hyp && sequent.hyp.length > 0;
    }

    /**
     * Check if promotion rule can be applied (!p rule)
     * @param {Object} sequent - Sequent data structure
     * @return {boolean} True if promotion rule can be applied
     */
    canApplyPromotion(sequent) {
        // Promotion requires all context formulas to be of the form !B (!Gamma)
        if (!sequent || !sequent.hyp || !sequent.cons || sequent.cons.length !== 1) {
            return false;
        }

        // Check that all context formulas are of the form !B
        for (let hypFormula of sequent.hyp) {
            if (hypFormula.type !== 'ofcourse') {
                return false;
            }
        }

        return true;
    }

    /**
     * Build a complete rule request from basic rule information
     * @param {Object} ruleConfig - Basic rule configuration
     * @param {jQuery} $li - List item element containing the formula
     * @param {Object} options - Display and interaction options
     * @return {Object} Complete rule request object
     */
    buildRuleRequest(ruleConfig, $li, options) {
        console.log('[ILL-MODE] Building rule request for config:', ruleConfig);
        console.log('[ILL-MODE] Options:', options);
        let ruleConfigCopy = JSON.parse(JSON.stringify(ruleConfig)); // deep copy
        
        // Handle ILL cut rule - transform to ILL-specific version
        if (ruleConfigCopy.rule === 'cut') {
            console.log('[ILL-MODE] Transforming cut rule to ill_cut');
            ruleConfigCopy.rule = 'ill_cut';
        }
        
        // Handle ILL axiom rule with applicability check
        if (ruleConfigCopy.rule === 'ill_axiom') {
            console.log('[ILL-MODE] Processing axiom rule');
            if ($li) {
                let formula = $li.data('formula');
                let $sequentTable = $li.closest('table');
                let $formulaList = $li.closest('ul');
                let isLeftSide = $formulaList.hasClass('hyp');
                console.log('[ILL-MODE] Checking axiom applicability for formula:', formula, 'on side:', isLeftSide ? 'left' : 'right');
                
                // Check if axiom rule is actually applicable now
                if (!this.isAxiomRuleApplicable($sequentTable, formula, isLeftSide)) {
                    console.log('[ILL-MODE] Axiom rule not applicable, returning null');
                    return null; // Don't apply the rule
                }
                console.log('[ILL-MODE] Axiom rule is applicable');
            }
        }
        
        let ruleRequest = { rule: ruleConfigCopy.rule };
        
        // Handle ILL cut rule parameters
        if (ruleConfigCopy.rule === 'ill_cut') {
            // Handle both cut-specific parameters and generic formula/formulaPosition
            if (ruleConfigCopy.formula || ruleConfigCopy.cutFormula) {
                ruleRequest['cutFormula'] = ruleConfigCopy.formula || ruleConfigCopy.cutFormula;
            }
            if (ruleConfigCopy.formulaPosition !== undefined || ruleConfigCopy.cutPosition !== undefined) {
                ruleRequest['cutPosition'] = ruleConfigCopy.formulaPosition !== undefined ? 
                    ruleConfigCopy.formulaPosition : ruleConfigCopy.cutPosition;
            }
        }

        // Handle axiom rule with notation unfolding
        if (ruleConfigCopy.rule === 'ill_axiom' && $li) {
            let formula = $li.data('formula');
            let atomName = formula['value'];
            if (formula['type'] === 'dual') {
                atomName = formula['value']['value'];
            }

            if (notationNameExists($li, atomName, null)) {
                ruleConfigCopy.rule = `unfold_${formula['type']}`;
                ruleConfigCopy.needPosition = true;
                ruleRequest.rule = ruleConfigCopy.rule;
            }
        }

        // Add sequent side information for ILL rules
        if ($li) {
            let $formulaList = $li.closest('ul');
            let isLeftSide = $formulaList.hasClass('hyp');
            let sequentSide = isLeftSide ? 'left' : 'right';
            ruleRequest['sequentSide'] = sequentSide;
            console.log('[ILL-MODE] Added sequent side:', sequentSide);
            
            // Special handling for ILL tensor_right rule: default to empty Gamma
            if (ruleConfigCopy.rule === 'ill_tensor_right' && sequentSide === 'right') {
                ruleRequest['contextSplit'] = [0]; // Empty Gamma, all context goes to Delta
                console.log('[ILL-MODE] Set default context split for tensor_right:', ruleRequest['contextSplit']);
            }
        }

        // Add position if needed
        if (ruleConfigCopy.needPosition && $li) {
            // Use position among formula items only, not all children
            let $formulaItems = $li.parent().children('li');
            ruleRequest['formulaPosition'] = $formulaItems.index($li);
            console.log('[ILL-MODE] Added formula position:', ruleRequest['formulaPosition']);
        }

        console.log('[ILL-MODE] Final rule request:', ruleRequest);
        return ruleRequest;
    }

    /**
     * Get display symbol for a rule in ILL mode
     * @param {string} rule - Rule name
     * @return {string} HTML string for rule symbol
     */
    getRuleSymbol(rule) {
        return ILL_RULES[rule] || LL_RULES[rule] || rule;
    }

    /**
     * Override applyRuleToSequent to handle cut rule transformation
     * @param {Object} ruleRequest - Rule application request  
     * @param {jQuery} $sequentTable - Sequent table element
     */
    applyRuleToSequent(ruleRequest, $sequentTable) {
        console.log('[ILL-MODE] Applying rule to sequent:', ruleRequest);
        // Transform cut rule to ill_cut if needed
        if (ruleRequest.rule === 'cut') {
            console.log('[ILL-MODE] Transforming cut rule for ILL');
            // Create a new rule request with ILL-specific parameters
            let illRuleRequest = {
                rule: 'ill_cut',
                cutFormula: ruleRequest.formula,
                cutPosition: ruleRequest.formulaPosition
            };
            console.log('[ILL-MODE] Transformed to ILL cut request:', illRuleRequest);
            
            // Apply the transformed rule
            super.applyRuleToSequent(illRuleRequest, $sequentTable);
        } else {
            console.log('[ILL-MODE] Applying rule normally:', ruleRequest.rule);
            // For non-cut rules, use normal processing
            super.applyRuleToSequent(ruleRequest, $sequentTable);
        }
        console.log('[ILL-MODE] Rule application completed');
    }

    /**
     * Get the mode name for this rule engine
     * @return {string} Mode name
     */
    getModeName() {
        return 'intuitionistic';
    }

    /**
     * Set up formula interaction for ILL mode with comma handling
     * @param {jQuery} $li - List item element containing the formula
     * @param {Object} formulaAsJson - Formula data structure
     * @param {Object} options - Display and interaction options
     */
    setupFormulaInteraction($li, formulaAsJson, options) {
        // Use the base class implementation for basic click handling
        super.setupFormulaInteraction($li, formulaAsJson, options);
        
        // Add ILL-specific comma interaction for context splitting
        if (options.withInteraction) {
            let $commaSpan = $li.find('span.comma');
            if ($commaSpan.length > 0) {
                this.setupCommaInteraction($commaSpan, $li, options);
            }
            
            // Don't add pre-space-clickable since first-point already handles this
            // The first-point element in sequent-core.js already provides clickable space before first formula
        }
    }

    /**
     * Set up clickable space before the first formula for empty Gamma
     * @param {jQuery} $li - The first list item element
     * @param {Object} options - Display options
     */
    setupPreFirstFormulaSpace($li, options) {
        // Create and prepend a clickable space span
        let $preSpaceSpan = $('<span>', {
            'class': 'pre-space-clickable',
            'html': '&nbsp;'
        });
        $li.prepend($preSpaceSpan);
        
        // Set up dynamic visibility based on tensor rule applicability
        let $sequentTable = $li.closest('table');
        this.updateCommaVisibility($preSpaceSpan, $sequentTable);
        
        // Add click handler
        $preSpaceSpan.on('click', (e) => {
            e.stopPropagation();
            
            let $currentSequentTable = $li.closest('table');
            
            if (!this.isTensorRuleApplicable($currentSequentTable)) {
                return;
            }
            
            // Enter comma selection mode with empty Gamma (position 0)
            this.enterCommaSelectionMode($currentSequentTable, 0);
        });
    }

    /**
     * Set up comma click functionality for ILL tensor rule context splitting
     * @param {jQuery} $commaSpan - The comma span element
     * @param {jQuery} $li - The list item containing the formula
     * @param {Object} options - Display options
     */
    setupCommaInteraction($commaSpan, $li, options) {
        // Check if this comma is in the context (left side)
        let $formulaList = $li.closest('ul');
        let isLeftSide = $formulaList.hasClass('hyp');
        
        if (!isLeftSide) {
            return; // Comma selection only applies to context formulas
        }
        
        // Set up dynamic comma visibility based on tensor rule applicability
        let $sequentTable = $li.closest('table');
        
        // Only proceed if we found a valid table
        if ($sequentTable.length > 0) {
            this.updateCommaVisibility($commaSpan, $sequentTable, options);
        }
        
        // Also trigger refresh for immediate visibility
        setTimeout(() => {
            let $container = $li.closest('.proof-container');
            if ($container.length > 0) {
                refreshILLTensorDotVisibility($container);
            }
        }, 150);
        
        // Add click handler that checks if tensor rule is applicable
        $commaSpan.on('click', (e) => {
            // Check if cut mode is enabled - if so, let cut mode handle the click
            let $proofDiv = $li.closest('.proof');
            let isCutModeEnabled = $proofDiv && $proofDiv.hasClass('cut-mode');
            
            if (isCutModeEnabled) {
                return; // Let cut mode handle this click
            }
            
            e.stopPropagation(); // Prevent event bubbling
            
            // Re-find the sequent table in case DOM has changed
            let $currentSequentTable = $li.closest('table');
            
            // Check if tensor rule is applicable (goal must be A⊗B)
            let tensorApplicable = this.isTensorRuleApplicable($currentSequentTable);
            
            if (!tensorApplicable) {
                return; // Only available when tensor rule can be applied
            }
            
            // Get comma position in context
            let $allFormulas = $formulaList.children('li');
            let commaPosition = $allFormulas.index($li) + 1; // Position after this formula
            
            // Enter comma selection mode
            this.enterCommaSelectionMode($currentSequentTable, commaPosition);
        });
    }

    /**
     * Update comma visibility based on tensor rule applicability
     * @param {jQuery} $commaSpan - The comma span element
     * @param {jQuery} $sequentTable - The sequent table element
     */
    updateCommaVisibility($commaSpan, $sequentTable, options = {}) {
        
        // Skip interaction setup if withInteraction is false
        if (options.withInteraction === false) {
            return;
        }
        
        // Clear any existing timeout to prevent race conditions
        if ($commaSpan.data('visibility-timeout')) {
            clearTimeout($commaSpan.data('visibility-timeout'));
        }
        
        // Always check for tensor rule applicability dynamically
        let timeoutId = setTimeout(() => {
            let sequent = $sequentTable.data('sequent') || $sequentTable.data('sequentWithoutPermutation');
            
            let tensorApplicable = this.isTensorRuleApplicable($sequentTable);
            let hasMultipleHyp = sequent && sequent.hyp && sequent.hyp.length > 1;
            let canSplit = tensorApplicable && hasMultipleHyp;
            
            // Check if cut mode is enabled - if so, don't interfere with cut mode handling
            let $proofDiv = $sequentTable.closest('.proof');
            let isCutModeEnabled = $proofDiv && $proofDiv.hasClass('cut-mode');
            
            if (isCutModeEnabled) {
                return;
            }
            
            // CRITICAL FIX: Recalculate isLastComma each time to handle rearrangement
            let $allContextLi = $sequentTable.find('.hyp li');
            let $currentLi = $commaSpan.closest('li');
            let currentIndex = $allContextLi.index($currentLi);
            let isLastComma = (currentIndex === $allContextLi.length - 1);
            
            // Edge case: If we can't find the current li or get invalid index, abort safely
            if (currentIndex < 0 || $allContextLi.length === 0) {
                $commaSpan.removeData('visibility-timeout');
                return;
            }
            
            if (canSplit) {
                $commaSpan.addClass('tensor-applicable');
                $commaSpan.attr('title', 'Click to select context split for tensor rule');
                
                if (isLastComma) {
                    // Store original content if not already stored or if it changed
                    let currentContent = $commaSpan.html();
                    
                    // Always store the current content before modifying (even if empty string)
                    if ($commaSpan.data('original-content') === undefined) {
                        $commaSpan.data('original-content', currentContent);
                    }
                    
                    // Replace content with just the dot only if not already a dot
                    if (currentContent !== '.') {
                        $commaSpan.html('.');
                    } else {
                    }
                } else {
                    // Non-last commas should not have dots - restore any dot content
                    let currentContent = $commaSpan.html();
                    let storedContent = $commaSpan.data('original-content');
                    
                    if (currentContent === '.') {
                        if (storedContent !== undefined) {
                            $commaSpan.html(storedContent);
                        } else {
                            $commaSpan.html('');
                        }
                    }
                }
            } else {
                $commaSpan.removeClass('tensor-applicable');
                $commaSpan.removeAttr('title');
                
                // Restore original content for any element that had dots
                let originalContent = $commaSpan.data('original-content');
                if (originalContent !== undefined && $commaSpan.html() === '.') {
                    $commaSpan.html(originalContent);
                    $commaSpan.removeData('original-content');
                } else {
                }
            }
            
            // Clear the timeout reference
            $commaSpan.removeData('visibility-timeout');
            
        }, 100); // Small delay to ensure sequent data is available
        
        // Store timeout reference to prevent race conditions
        $commaSpan.data('visibility-timeout', timeoutId);
    }

    /**
     * Update first-point visibility based on tensor rule applicability
     * @param {jQuery} $firstPoint - The first-point span element
     * @param {jQuery} $sequentTable - The sequent table element
     */
    updateFirstPointVisibility($firstPoint, $sequentTable, options = {}) {
        // Skip interaction setup if withInteraction is false
        if (options.withInteraction === false) {
            return;
        }
        
        // Always check for tensor rule applicability dynamically
        setTimeout(() => {
            let sequent = $sequentTable.data('sequent') || $sequentTable.data('sequentWithoutPermutation');
            let canSplit = this.isTensorRuleApplicable($sequentTable) && sequent && sequent.hyp && sequent.hyp.length > 1;
            
            if (canSplit) {
                $firstPoint.addClass('tensor-applicable');
                $firstPoint.attr('title', 'Click to select empty Gamma for tensor rule');
                
                // Store original content if not already stored
                if (!$firstPoint.data('original-content')) {
                    $firstPoint.data('original-content', $firstPoint.html());
                }
                
                // Replace content with just the dot
                $firstPoint.html('.');
            } else {
                $firstPoint.removeClass('tensor-applicable');
                $firstPoint.removeAttr('title');
                
                // Restore original content
                let originalContent = $firstPoint.data('original-content');
                if (originalContent !== undefined) {
                    $firstPoint.html(originalContent);
                }
            }
        }, 100); // Small delay to ensure sequent data is available
    }

    /**
     * Check if tensor rule is applicable to the current sequent
     * @param {jQuery} $sequentTable - The sequent table element
     * @return {boolean} True if tensor rule can be applied
     */
    isTensorRuleApplicable($sequentTable) {
        let sequent = $sequentTable.data('sequent') || $sequentTable.data('sequentWithoutPermutation');
        
        if (!sequent || !sequent.cons || sequent.cons.length !== 1) {
            return false;
        }
        
        let goalFormula = sequent.cons[0];
        return goalFormula.type === 'tensor';
    }

    /**
     * Refresh all comma visibility after DOM rearrangement
     * @param {jQuery} $formulaList - The sortable formula list that was rearranged
     */
    refreshAllCommaVisibility($formulaList) {
        // Edge case: Prevent recursion by checking if we're already in a refresh cycle
        if ($formulaList.data('refreshing-commas')) {
            return;
        }
        
        // Mark as refreshing to prevent recursion
        $formulaList.data('refreshing-commas', true);
        
        try {
            // Edge case: Check if the formula list exists and has formulas
            if (!$formulaList.length || $formulaList.find('li').length === 0) {
                return;
            }
            
            // Clear all stored original-content data and reset content since positions changed
            $formulaList.find('span.comma').each(function() {
                let $commaSpan = $(this);
                
                $commaSpan.removeData('original-content');
                
                // CRITICAL FIX: Reset all comma content to empty after rearrangement
                // This ensures no comma retains stale dot content from previous positions
                if ($commaSpan.html() === '.') {
                    $commaSpan.html('');
                }
                
                // Clear any pending timeouts
                if ($commaSpan.data('visibility-timeout')) {
                    clearTimeout($commaSpan.data('visibility-timeout'));
                    $commaSpan.removeData('visibility-timeout');
                }
            });
            
            // Get the sequent table
            let $sequentTable = $formulaList.closest('table');
            
            // Edge case: Verify we have a valid sequent table
            if (!$sequentTable.length) {
                return;
            }
            
            // Refresh all comma visibility with fresh position calculation
            let commasToUpdate = $formulaList.find('span.comma');
            
            commasToUpdate.each((index, element) => {
                let $commaSpan = $(element);
                this.updateCommaVisibility($commaSpan, $sequentTable, {withInteraction: true});
            });
            
        } finally {
            // Always clear the refreshing flag
            setTimeout(() => {
                $formulaList.removeData('refreshing-commas');
            }, 200);
        }
    }

    /**
     * Enter comma selection mode for tensor rule context splitting
     * @param {jQuery} $sequentTable - The sequent table element
     * @param {number} commaPosition - Position where Gamma ends (0-based)
     */
    enterCommaSelectionMode($sequentTable, commaPosition) {
        let $container = $sequentTable.closest('.proof-container');
        
        // Clear any existing selection state
        this.clearCommaSelectionMode($sequentTable);
        
        // Mark the sequent table as in comma selection mode
        $sequentTable.addClass('comma-selection-mode');
        $sequentTable.data('selectedCommaPosition', commaPosition);
        
        // Highlight the selected range (Gamma)
        this.highlightGammaRange($sequentTable, commaPosition);
        
        // Add visual feedback message
        this.displayCommaSelectionMessage($container, commaPosition);
        
        // Apply tensor rule automatically with the selected split
        this.applyTensorRuleWithSplit($sequentTable, commaPosition);
    }

    /**
     * Clear comma selection mode and remove all visual indicators
     * @param {jQuery} $sequentTable - The sequent table element
     */
    clearCommaSelectionMode($sequentTable) {
        let $container = $sequentTable.closest('.proof-container');
        
        // Remove mode class and data
        $sequentTable.removeClass('comma-selection-mode');
        $sequentTable.removeData('selectedCommaPosition');
        
        // Clear highlighting
        $sequentTable.find('.formula-gamma, .formula-delta').removeClass('formula-gamma formula-delta');
        
        // Clear any comma selection messages
        $container.find('.comma-selection-message').remove();
    }

    /**
     * Highlight formulas in Gamma and Delta ranges
     * @param {jQuery} $sequentTable - The sequent table element
     * @param {number} commaPosition - Position where Gamma ends
     */
    highlightGammaRange($sequentTable, commaPosition) {
        let $contextFormulas = $sequentTable.find('ul.hyp li');
        
        $contextFormulas.each(function(index) {
            let $formula = $(this);
            if (index < commaPosition) {
                $formula.addClass('formula-gamma');
            } else {
                $formula.addClass('formula-delta');
            }
        });
    }

    /**
     * Display message about comma selection
     * @param {jQuery} $container - The proof container element
     * @param {number} commaPosition - Position where Gamma ends
     */
    displayCommaSelectionMessage($container, commaPosition) {
        let message = `Context split selected: Γ contains ${commaPosition} formula(s), Δ contains the rest.`;
        
        let $message = $('<div>', {'class': 'comma-selection-message pedagogic-message info'});
        $message.append($('<div>', {'class': 'message'}).text(message));
        
        let $proofDiv = $container.children('div.proof');
        if ($proofDiv.length) {
            $message.insertAfter($proofDiv);
        } else {
            $container.append($message);
        }
        
        // Auto-hide message after 3 seconds
        setTimeout(function() {
            $message.fadeOut();
        }, 3000);
    }

    /**
     * Apply tensor rule with the specified context split
     * @param {jQuery} $sequentTable - The sequent table element
     * @param {number} commaPosition - Position where Gamma ends
     */
    applyTensorRuleWithSplit($sequentTable, commaPosition) {
        console.log('[ILL-MODE] Applying tensor rule with split at position:', commaPosition);
        let ruleRequest = {
            rule: 'ill_tensor_right',
            sequentSide: 'right',
            contextSplit: [commaPosition]
        };
        console.log('[ILL-MODE] Tensor rule request:', ruleRequest);
        
        // Apply the rule
        this.applyRuleToSequent(ruleRequest, $sequentTable);
        
        // Clear selection mode after rule application
        console.log('[ILL-MODE] Clearing comma selection mode after tensor rule');
        this.clearCommaSelectionMode($sequentTable);
    }
}

// Intuitionistic Linear Logic rule symbols for display
const ILL_RULES = {
    'ill_axiom': '<span class="italic">ax</span>',
    'ill_tensor_right': '⊗<sub>R</sub>',
    'ill_tensor_left': '⊗<sub>L</sub>',
    'ill_tensor': '⊗<sub>R</sub>',
    'ill_with_right': '&<sub>R</sub>',
    'ill_with': '&<sub>R</sub>',
    'ill_with_left_1': '&<sub>L1</sub>',
    'ill_with_left_2': '&<sub>L2</sub>',
    'ill_plus_left': '⊕<sub>L</sub>',
    'ill_plus_right_1': '⊕<sub>R1</sub>',
    'ill_plus_right_2': '⊕<sub>R2</sub>',
    'ill_lollipop_right': '⊸<sub>R</sub>',
    'ill_lollipop': '⊸<sub>R</sub>',
    'ill_lollipop_left': '⊸<sub>L</sub>',
    'ill_one_right': '1<sub>R</sub>',
    'ill_one_left': '1<sub>L</sub>',
    'ill_top': '⊤',
    'ill_cut': '<span class="italic">cut</span>',
    'ill_weakening': '!<span class="italic">w</span>',
    'ill_contraction': '!<span class="italic">c</span>',
    'ill_dereliction': '!<span class="italic">d</span>',
    'ill_promotion': '!<span class="italic">p</span>'
};

/**
 * Update comma visibility for all sequents in a container
 * @param {jQuery} $container - The proof container element
 */
function updateAllCommaVisibility($container) {
    let ruleEngine = $container.data('ruleEngine');
    let options = $container.data('options') || {};
    
    if (!ruleEngine || ruleEngine.getModeName() !== 'intuitionistic') {
        return; // Only relevant for ILL mode
    }
    
    $container.find('.proof table').each(function() {
        let $sequentTable = $(this);
        
        $sequentTable.find('.hyp li span.comma').each(function() {
            ruleEngine.updateCommaVisibility($(this), $sequentTable, options);
        });
        
        // Pre-space functionality removed - first-point element handles space before first formula
    });
}