// ABSTRACT RULE ENGINE
// Base class for Linear Logic rule systems
// Provides common interface and shared functionality for LL and ILL modes

/**
 * Abstract base class for rule engines
 * Each logic mode (LL, ILL) must extend this class and implement the abstract methods
 */
class RuleEngine {
    constructor() {
        this.ruleSymbols = {};
        this.modeName = 'abstract';
    }

    // Abstract methods that must be implemented by subclasses
    
    /**
     * Get applicable rules for a formula in the current context
     * @param {Object} formulaAsJson - Formula data structure
     * @param {Object} options - Display and interaction options
     * @param {boolean} isLeftSide - Whether formula is on left side of turnstile
     * @param {jQuery} $li - List item element containing the formula
     * @return {Array} Array of rule event configurations
     */
    getRules(formulaAsJson, options, isLeftSide, $li) {
        throw new Error('getRules must be implemented by subclass');
    }

    /**
     * Check if a rule can be applied to the given sequent
     * @param {Object} ruleRequest - Rule application request
     * @param {Object} sequent - Sequent data structure
     * @return {boolean} True if rule is applicable
     */
    canApplyRule(ruleRequest, sequent) {
        throw new Error('canApplyRule must be implemented by subclass');
    }

    /**
     * Build a complete rule request from basic rule information
     * @param {Object} ruleConfig - Basic rule configuration
     * @param {jQuery} $li - List item element containing the formula
     * @param {Object} options - Display and interaction options
     * @return {Object} Complete rule request object
     */
    buildRuleRequest(ruleConfig, $li, options) {
        throw new Error('buildRuleRequest must be implemented by subclass');
    }

    /**
     * Get display symbol for a rule
     * @param {string} rule - Rule name
     * @return {string} HTML string for rule symbol
     */
    getRuleSymbol(rule) {
        throw new Error('getRuleSymbol must be implemented by subclass');
    }

    // Common functionality that can be shared across modes

    /**
     * Apply a rule to a sequent (common workflow)
     * @param {Object} ruleRequest - Rule application request
     * @param {jQuery} $sequentTable - Sequent table element
     */
    applyRuleToSequent(ruleRequest, $sequentTable) {
        console.log('DEBUG: RuleEngine.applyRuleToSequent called with:', ruleRequest);
        console.log('DEBUG: Rule engine mode:', this.getModeName());
        // Just delegate to the global applyRule function
        // which handles all the backend communication
        applyRule(ruleRequest, $sequentTable);
    }

    /**
     * Validate that a rule request is well-formed
     * @param {Object} ruleRequest - Rule application request
     * @param {Object} sequent - Sequent data structure
     * @return {boolean} True if request is valid
     */
    validateRuleApplication(ruleRequest, sequent) {
        if (!ruleRequest || !ruleRequest.rule) {
            return false;
        }

        // Basic validation - subclasses can override for more specific checks
        return this.canApplyRule(ruleRequest, sequent);
    }

    /**
     * Check if this rule engine handles the given rule
     * @param {string} ruleName - Name of the rule
     * @return {boolean} True if this engine handles the rule
     */
    handlesRule(ruleName) {
        return ruleName in this.ruleSymbols;
    }

    /**
     * Get the mode name for this rule engine
     * @return {string} Mode name
     */
    getModeName() {
        return this.modeName;
    }

    /**
     * Setup formula interaction based on applicable rules
     * @param {jQuery} $li - List item element containing the formula
     * @param {Object} formulaAsJson - Formula data structure
     * @param {Object} options - Display and interaction options
     */
    setupFormulaInteraction($li, formulaAsJson, options) {
        console.log('DEBUG: Setting up formula interaction for:', formulaAsJson.type, 'mode:', this.getModeName());
        // Determine which side of the turnstile we're on
        let $formulaList = $li.closest('ul');
        let isLeftSide = $formulaList.hasClass('hyp');
        let rules = this.getRules(formulaAsJson, options, isLeftSide, $li);
        console.log('DEBUG: Got rules for formula:', rules);

        if (rules.length === 0) {
            console.log('DEBUG: No rules found for formula, skipping interaction setup');
            return; // No rules to apply
        }

        // Add hover styling
        $li.find('span.main-formula').first().addClass('hoverable');
        
        // Set up click handlers for each rule
        for (let ruleEvent of rules) {
            let $spanForEvent = $li.find('span.' + ruleEvent.element).first();
            console.log('DEBUG: Setting up click handler for element:', ruleEvent.element);

            // Add clickable styling
            $spanForEvent.addClass('clickable');
            if (ruleEvent.element !== 'main-formula') {
                $spanForEvent.addClass('highlightableExpr');
            }

            // Add click events
            if (ruleEvent.onclick.length === 1) {
                // Single click only
                $spanForEvent.on('click', this.buildApplyRuleCallback(ruleEvent.onclick[0], $li, options));
            } else {
                // Single click AND double click
                let singleClickCallback = this.buildApplyRuleCallback(ruleEvent.onclick[0], $li, options);
                let doubleClickCallback = this.buildApplyRuleCallback(ruleEvent.onclick[1], $li, options);
                addClickAndDoubleClickEvent($spanForEvent, singleClickCallback, doubleClickCallback);
            }
        }
    }

    /**
     * Build a callback function for rule application
     * @param {Object} ruleConfig - Rule configuration
     * @param {jQuery} $li - List item element
     * @param {Object} options - Display options
     * @return {Function} Callback function
     */
    buildApplyRuleCallback(ruleConfig, $li, options) {
        return () => {
            console.log('DEBUG: Formula clicked, rule config:', ruleConfig);
            let ruleRequest = this.buildRuleRequest(ruleConfig, $li, options);
            console.log('DEBUG: Built rule request:', ruleRequest);
            
            if (!ruleRequest) {
                console.log('DEBUG: Rule request is null, not applying rule');
                return;
            }
            
            if (options.withInteraction) {
                console.log('DEBUG: Applying rule with interaction enabled');
                this.applyRuleToSequent(ruleRequest, $li.closest('table'));
            } else if (options.proofTransformation?.value) {
                console.log('DEBUG: Applying transformation');
                let $sequentTable = $li.closest('table');
                applyTransformation($sequentTable, {
                    transformation: ruleConfig.transformation, 
                    ruleRequest
                });
            }
        };
    }
}

// Export for module system
if (typeof module !== 'undefined' && module.exports) {
    module.exports = RuleEngine;
}