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
                return [{'element': 'main-formula', 'onclick': [{'rule': 'axiom_ill', 'needPosition': false}]}];

            case 'tensor':
                if (isLeftSide) {
                    // ILL: Left side tensor elimination
                    return [{'element': 'main-formula', 'onclick': [{'rule': 'tensor_left', 'needPosition': true}]}];
                } else {
                    // ILL: Right side tensor introduction
                    return [{'element': 'main-formula', 'onclick': [{'rule': 'tensor_right', 'needPosition': true}]}];
                }

            case 'par':
                // Par is only available in classical LL, not in ILL
                return [];
                
            case 'with':
                if (isLeftSide) {
                    // ILL: Left side with elimination (choose left or right sub-formula)
                    return [
                        {'element': 'left-formula', 'onclick': [{'rule': 'with_left_1', 'needPosition': true}]},
                        {'element': 'right-formula', 'onclick': [{'rule': 'with_left_2', 'needPosition': true}]}
                    ];
                } else {
                    // ILL: Right side with introduction
                    return [{'element': 'main-formula', 'onclick': [{'rule': 'with_right', 'needPosition': true}]}];
                }

            case 'plus':
                if (isLeftSide) {
                    // ILL: Left side plus elimination
                    return [{'element': 'main-formula', 'onclick': [{'rule': 'plus_left', 'needPosition': true}]}];
                } else {
                    // ILL: Right side plus introduction (choose left or right sub-formula)
                    return [
                        {'element': 'left-formula', 'onclick': [{'rule': 'plus_right_1', 'needPosition': true}]},
                        {'element': 'right-formula', 'onclick': [{'rule': 'plus_right_2', 'needPosition': true}]}
                    ];
                }

            case 'lollipop':
                if (isLeftSide) {
                    // ILL: Left side lollipop elimination (modus ponens)
                    return [{'element': 'main-formula', 'onclick': [{'rule': 'lollipop_left', 'needPosition': true}]}];
                } else {
                    // ILL: Right side lollipop introduction (implication introduction)
                    return [{'element': 'main-formula', 'onclick': [{'rule': 'lollipop_right', 'needPosition': true}]}];
                }

            case 'one':
                // In ILL mode, one rule only applicable on right side with empty context
                if (!isLeftSide && $li && this.isOneRuleApplicable($li.closest('table'))) {
                    return [{'element': 'main-formula', 'onclick': [{'rule': formulaAsJson.type, 'needPosition': false}]}];
                }
                return [];

            case 'zero':
                // Zero rule does not exist
                return [];

            case 'top':
                // In ILL mode, top rule is always applicable on right side
                if (!isLeftSide) {
                    return [{'element': 'main-formula', 'onclick': [{'rule': formulaAsJson.type, 'needPosition': true}]}];
                }
                return [];

            case 'bottom':
                // Bottom rule in ILL
                return [{'element': 'main-formula', 'onclick': [{'rule': formulaAsJson.type, 'needPosition': true}]}];

            case 'ofcourse':
            case 'whynot':
                // Exponentials not typically used in basic ILL
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
        // ILL transformation rules would be similar to LL but with directional restrictions
        // For now, return empty array as transformations are less common in ILL
        return [];
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
            case 'axiom':
                return this.canApplyAxiom(sequent);
            case 'one':
                return sequent.hyp.length === 0 && sequent.cons.length === 1;
            case 'top':
                return sequent.cons.length === 1;
            case 'tensor_right':
                return this.canApplyTensorRight(sequent);
            case 'with_right':
                return sequent.cons.length === 1;
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
     * Check if one rule is applicable (requires empty context)
     * @param {jQuery} $sequentTable - Sequent table element
     * @return {boolean} True if one rule can be applied
     */
    isOneRuleApplicable($sequentTable) {
        let sequent = $sequentTable.data('sequent') || $sequentTable.data('sequentWithoutPermutation');
        
        if (!sequent || !sequent.hyp || !sequent.cons || sequent.cons.length !== 1) {
            return false;
        }

        // One rule requires empty context
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
     * Build a complete rule request from basic rule information
     * @param {Object} ruleConfig - Basic rule configuration
     * @param {jQuery} $li - List item element containing the formula
     * @param {Object} options - Display and interaction options
     * @return {Object} Complete rule request object
     */
    buildRuleRequest(ruleConfig, $li, options) {
        let ruleConfigCopy = JSON.parse(JSON.stringify(ruleConfig)); // deep copy
        
        // Handle ILL axiom rule with applicability check
        if (ruleConfigCopy.rule === 'axiom_ill') {
            if ($li) {
                let formula = $li.data('formula');
                let $sequentTable = $li.closest('table');
                let $formulaList = $li.closest('ul');
                let isLeftSide = $formulaList.hasClass('hyp');
                
                // Check if axiom rule is actually applicable now
                if (this.isAxiomRuleApplicable($sequentTable, formula, isLeftSide)) {
                    ruleConfigCopy.rule = 'axiom'; // Convert to regular axiom rule
                } else {
                    return null; // Don't apply the rule
                }
            } else {
                // For turnstile clicks, just convert to regular axiom
                ruleConfigCopy.rule = 'axiom';
            }
        }
        
        let ruleRequest = { rule: ruleConfigCopy.rule };

        // Handle axiom rule with notation unfolding
        if (ruleConfigCopy.rule === 'axiom' && $li) {
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
            
            // Special handling for ILL tensor_right rule: default to empty Gamma
            if (ruleConfigCopy.rule === 'tensor_right' && sequentSide === 'right') {
                ruleRequest['contextSplit'] = [0]; // Empty Gamma, all context goes to Delta
            }
        }

        // Add position if needed
        if (ruleConfigCopy.needPosition && $li) {
            ruleRequest['formulaPosition'] = $li.parent().children().index($li);
        }

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
        }
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
        this.updateCommaVisibility($commaSpan, $sequentTable);
        
        // Add click handler that checks if tensor rule is applicable
        $commaSpan.on('click', (e) => {
            e.stopPropagation(); // Prevent event bubbling
            
            // Re-find the sequent table in case DOM has changed
            let $currentSequentTable = $li.closest('table');
            
            // Check if tensor rule is applicable (goal must be A⊗B)
            if (!this.isTensorRuleApplicable($currentSequentTable)) {
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
    updateCommaVisibility($commaSpan, $sequentTable) {
        // Always check for tensor rule applicability dynamically
        setTimeout(() => {
            if (this.isTensorRuleApplicable($sequentTable)) {
                $commaSpan.addClass('tensor-applicable');
                $commaSpan.attr('title', 'Click to select context split for tensor rule');
            } else {
                $commaSpan.removeClass('tensor-applicable');
                $commaSpan.removeAttr('title');
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
        let ruleRequest = {
            rule: 'tensor_right',
            sequentSide: 'right',
            contextSplit: [commaPosition]
        };
        
        // Apply the rule
        this.applyRuleToSequent(ruleRequest, $sequentTable);
        
        // Clear selection mode after rule application
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
    'ill_one': '1',
    'ill_top': '⊤'
};

/**
 * Update comma visibility for all sequents in a container
 * @param {jQuery} $container - The proof container element
 */
function updateAllCommaVisibility($container) {
    let ruleEngine = $container.data('ruleEngine');
    
    if (!ruleEngine || ruleEngine.getModeName() !== 'intuitionistic') {
        return; // Only relevant for ILL mode
    }
    
    $container.find('.proof table').each(function() {
        let $sequentTable = $(this);
        
        $sequentTable.find('.hyp li span.comma').each(function() {
            ruleEngine.updateCommaVisibility($(this), $sequentTable);
        });
    });
}