// LINEAR LOGIC MODE
// Classic Linear Logic implementation extending the abstract rule engine
// Contains all LL-specific rule logic, symbols, and behavior

/**
 * Classic Linear Logic Rule Engine
 * Implements standard LL rules and interactions
 */
class LLRuleEngine extends RuleEngine {
    constructor() {
        super();
        this.ruleSymbols = LL_RULES;
        this.modeName = 'classical';
    }

    /**
     * Get applicable rules for a formula in LL mode
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
            return this.getInteractiveRules(formulaAsJson, isLeftSide);
        } else if (options.proofTransformation?.value) {
            return this.getTransformationRules(formulaAsJson);
        }

        return [];
    }

    /**
     * Get interactive rules for LL mode
     * @param {Object} formulaAsJson - Formula data structure
     * @param {boolean} isLeftSide - Whether formula is on left side
     * @return {Array} Array of rule event configurations
     */
    getInteractiveRules(formulaAsJson, isLeftSide) {
        switch (formulaAsJson.type) {
            case 'litt':
            case 'dual':
                return [{'element': 'main-formula', 'onclick': [{'rule': 'axiom', 'needPosition': false}]}];

            case 'tensor':
                return [{'element': 'main-formula', 'onclick': [{'rule': 'tensor', 'needPosition': true}]}];

            case 'par':
                return [{'element': 'main-formula', 'onclick': [{'rule': 'par', 'needPosition': true}]}];
                
            case 'with':
                return [{'element': 'main-formula', 'onclick': [{'rule': 'with', 'needPosition': true}]}];

            case 'plus':
                if (isLeftSide) {
                    return [{'element': 'main-formula', 'onclick': [{'rule': 'plus_left', 'needPosition': true}]}];
                } else {
                    return [{'element': 'main-formula', 'onclick': [{'rule': 'plus_right', 'needPosition': true}]}];
                }

            case 'lollipop':
                return [{'element': 'main-formula', 'onclick': [{'rule': 'lollipop', 'needPosition': true}]}];

            case 'one':
            case 'zero':
                return [{'element': 'main-formula', 'onclick': [{'rule': formulaAsJson.type, 'needPosition': false}]}];

            case 'top':
            case 'bottom':
                return [{'element': 'main-formula', 'onclick': [{'rule': formulaAsJson.type, 'needPosition': true}]}];

            case 'ofcourse':
                return [{'element': 'main-formula', 'onclick': [{'rule': 'promotion', 'needPosition': true}]}];

            case 'whynot':
                return [
                    {
                        'element': 'primaryConnector', 'onclick': [
                            {'rule': 'weakening', 'needPosition': true},
                            {'rule': 'contraction', 'needPosition': true}
                        ]
                    },
                    {
                        'element': 'sub-formula', 'onclick': [
                            {'rule': 'dereliction', 'needPosition': true},
                            {'rule': 'contraction', 'needPosition': true}
                        ]
                    }
                ];

            default:
                return [];
        }
    }

    /**
     * Get transformation rules for LL mode
     * @param {Object} formulaAsJson - Formula data structure
     * @return {Array} Array of rule event configurations
     */
    getTransformationRules(formulaAsJson) {
        switch (formulaAsJson.type) {
            case 'par':
            case 'with':
                return [{'element': 'main-formula', 'onclick': [{'rule': formulaAsJson.type, 'needPosition': true, 'transformation': 'apply_reversible_first'}]}];

            case 'top':
            case 'bottom':
                return [{'element': 'main-formula', 'onclick': [{'rule': formulaAsJson.type, 'needPosition': true, 'transformation': 'apply_reversible_first'}]}];

            case 'ofcourse':
                return [{'element': 'main-formula', 'onclick': [{'rule': 'promotion', 'needPosition': true, 'transformation': 'apply_reversible_first'}]}];

            default:
                return [];
        }
    }

    /**
     * Check if a rule can be applied to the given sequent in LL mode
     * @param {Object} ruleRequest - Rule application request
     * @param {Object} sequent - Sequent data structure
     * @return {boolean} True if rule is applicable
     */
    canApplyRule(ruleRequest, sequent) {
        if (!ruleRequest || !ruleRequest.rule) {
            return false;
        }

        // Basic LL rule validation
        switch (ruleRequest.rule) {
            case 'axiom':
                return this.canApplyAxiom(sequent);
            case 'one':
                return sequent.hyp.length === 0 && sequent.cons.length === 1;
            case 'zero':
                return false; // Zero rule does not exist in LL
            default:
                return true; // Most LL rules are permissive
        }
    }

    /**
     * Check if axiom rule can be applied
     * @param {Object} sequent - Sequent data structure
     * @return {boolean} True if axiom is applicable
     */
    canApplyAxiom(sequent) {
        // In LL, axiom rule is more permissive than in ILL
        // Can be applied when there are matching formulas
        if (!sequent.hyp || !sequent.cons || sequent.hyp.length === 0 || sequent.cons.length === 0) {
            return false;
        }

        // Check for matching literals or duals
        for (let hypFormula of sequent.hyp) {
            for (let consFormula of sequent.cons) {
                if (formulasMatch(hypFormula, consFormula)) {
                    return true;
                }
            }
        }

        return false;
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

        // Add position if needed
        if (ruleConfigCopy.needPosition && $li) {
            ruleRequest['formulaPosition'] = $li.parent().children().index($li);
        }

        return ruleRequest;
    }

    /**
     * Get display symbol for a rule in LL mode
     * @param {string} rule - Rule name
     * @return {string} HTML string for rule symbol
     */
    getRuleSymbol(rule) {
        return LL_RULES[rule] || rule;
    }

    /**
     * Set up formula interaction for LL mode
     * @param {jQuery} $li - List item element containing the formula
     * @param {Object} formulaAsJson - Formula data structure
     * @param {Object} options - Display and interaction options
     */
    setupFormulaInteraction($li, formulaAsJson, options) {
        // Use the base class implementation which calls our getRules method
        super.setupFormulaInteraction($li, formulaAsJson, options);
        
        // No additional LL-specific interaction setup needed
    }
}

// Linear Logic rule symbols for display
const LL_RULES = {
    'axiom': '<span class="italic">ax</span>',          // Axiom rule: A, A^
    'tensor': '⊗',                                      // Tensor rule: A⊗B
    'par': '<span class="flip">&</span>',               // Par rule: A⅋B  
    'with': '&',                                        // With rule: A&B
    'plus_left': '⊕<sub>1</sub>',                      // Plus left: A⊕B elimination from context
    'plus_right': '⊕<sub>2</sub>',                     // Plus right: A⊕B introduction to conclusion
    'lollipop': '⊸',                                   // Lollipop rule: A⊸B
    'one': '1',                                         // One rule: multiplicative unit
    'bottom': '⊥',                                      // Bottom rule: multiplicative zero
    'top': '⊤',                                         // Top rule: additive unit
    // zero does not exist (additive zero has no rule)
    'promotion': '!',                                   // Promotion rule: !A
    'dereliction': '?<span class="italic">d</span>',   // Dereliction: ?A becomes A
    'contraction': '?<span class="italic">c</span>',   // Contraction: ?A becomes ?A,?A
    'weakening': '?<span class="italic">w</span>',     // Weakening: ?A becomes nothing
    'exchange': '<span class="italic">ech</span>',     // Exchange: swap formulas
    'cut': '<span class="italic">cut</span>',          // Cut rule: eliminate formula
    'unfold_litt': '<span class="italic">def</span>',  // Unfold literal notation
    'unfold_dual': '<span class="italic">def</span>'   // Unfold dual notation
};