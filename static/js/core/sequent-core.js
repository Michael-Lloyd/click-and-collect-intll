// SEQUENT CORE MODULE
// Mode-agnostic sequent rendering and basic interaction functionality
// Extracted from the original sequent.js to separate core logic from mode-specific behavior

// Formula display constants (mode-agnostic)
const UNARY_CONNECTORS = {
    'negation': '¬',
    'ofcourse': '!',
    'whynot': '?'
};

const BINARY_CONNECTORS = {
    'implication': '<span class="binary-connector">→</span>',
    'conjunction': '<span class="binary-connector">∧</span>',
    'disjunction': '<span class="binary-connector">∨</span>',
    'tensor': '<span class="binary-connector">⊗</span>',
    'par': '<span class="binary-connector flip">&</span>',
    'with': '<span class="binary-connector">&</span>',
    'plus': '<span class="binary-connector">⊕</span>',
    'lollipop': '<span class="binary-connector">⊸</span>'
};

const NEUTRAL_ELEMENTS = {
    'true': 'true',
    'false': 'false',
    'one': '1',
    'bottom': '⊥',
    'top': '⊤',
    'zero': '0'
};

/**
 * Create a sequent display element (mode-agnostic)
 * @param {Object} sequent - Sequent data structure
 * @param {jQuery} $sequentTable - Table element containing the sequent
 * @param {Object} options - Display options
 * @param {RuleEngine} ruleEngine - Rule engine for interaction handling
 * @return {jQuery} Sequent div element
 */
function createSequent(sequent, $sequentTable, options, ruleEngine = null) {
    let $sequentDiv = $('<div>', {'class': 'sequent'});

    // Create hypothesis (left side) if present
    if ('hyp' in sequent) {
        createFormulaList(sequent, 'hyp', $sequentDiv, options, ruleEngine);
    }

    // Create turnstile
    let $thesisSpan = $('<span class="turnstile">⊢</span>');
    if (options.withInteraction && ruleEngine) {
        $thesisSpan.addClass('clickable');
        addClickAndDoubleClickEvent($thesisSpan, function () {
            // No action on single click - turnstile is only for auto-prover via double-click
        }, function () {
            autoProveSequent($sequentTable);
        });
    }
    $sequentDiv.append($thesisSpan);

    // Create conclusion (right side) if present
    if ('cons' in sequent) {
        createFormulaList(sequent, 'cons', $sequentDiv, options, ruleEngine);
    }

    return $sequentDiv;
}

/**
 * Create a formula list (hypothesis or conclusion)
 * @param {Object} sequent - Sequent data structure
 * @param {string} sequentPart - 'hyp' or 'cons'
 * @param {jQuery} $sequentDiv - Container div element
 * @param {Object} options - Display options
 * @param {RuleEngine} ruleEngine - Rule engine for interaction handling
 */
function createFormulaList(sequent, sequentPart, $sequentDiv, options, ruleEngine = null) {
    let $ul = $('<ul>', {'class': ['commaList ' + sequentPart]});
    $sequentDiv.append($ul);

    let $firstPoint = $('<span>', {'class': 'first-point'});
    $ul.prepend($firstPoint);

    // Set up sortable interaction if enabled
    if (options.withInteraction) {
        $ul.sortable({
            helper: 'clone',
            axis: 'x',
            opacity: 0.2,
            items: 'li', // Only li elements (formulas) are sortable, not spans like first-point
            start: function(e, ui) {
                ui.placeholder.width(ui.item.width());
            },
            update: function(e, ui) {
                // Immediate refresh on position change for better responsiveness
                let isILLMode = ruleEngine && ruleEngine.getModeName() === 'intuitionistic';
                if (isILLMode && sequentPart === 'hyp') {
                    let $container = $ul.closest('.proof-container');
                    let ruleEngineInstance = $container.data('ruleEngine');
                    if (ruleEngineInstance && typeof ruleEngineInstance.refreshAllCommaVisibility === 'function') {
                        // Small delay to let DOM settle
                        setTimeout(() => {
                            ruleEngineInstance.refreshAllCommaVisibility($ul);
                        }, 50);
                    }
                }
            },
            stop: function(e, ui) {
                // Check if we're in ILL mode and this is the context side
                let isILLMode = ruleEngine && ruleEngine.getModeName() === 'intuitionistic';
                if (isILLMode && sequentPart === 'hyp') {
                    let $container = $ul.closest('.proof-container');
                    // Call our enhanced comma refresh first, then the general refresh
                    let ruleEngineInstance = $container.data('ruleEngine');
                    if (ruleEngineInstance && typeof ruleEngineInstance.refreshAllCommaVisibility === 'function') {
                        ruleEngineInstance.refreshAllCommaVisibility($ul);
                    }
                    setTimeout(() => {
                        refreshILLTensorDotVisibility($container);
                    }, 150); // Slightly longer delay to let our refresh complete first
                }
            }
        });
        
        // Only add cut mode to left side (context) in ILL mode
        let isILLMode = ruleEngine && ruleEngine.getModeName() === 'intuitionistic';
        if (!isILLMode || sequentPart === 'hyp') {
            addCutOnClick($firstPoint, true);
        }
        
        // In ILL mode, also set up tensor rule interaction for first-point on left side
        if (isILLMode && sequentPart === 'hyp') {
            // Add tensor rule handling to first-point
            $firstPoint.on('click', (e) => {
                // Check if cut mode is enabled - if so, let cut mode handle the click
                let $proofDiv = $firstPoint.closest('.proof');
                let isCutModeEnabled = $proofDiv && $proofDiv.hasClass('cut-mode');
                
                if (isCutModeEnabled) {
                    return; // Let cut mode handle this click
                }
                
                e.stopPropagation();
                
                let $sequentTable = $firstPoint.closest('table');
                
                // Check if tensor rule is applicable
                let tensorApplicable = ruleEngine && ruleEngine.isTensorRuleApplicable && ruleEngine.isTensorRuleApplicable($sequentTable);
                
                if (tensorApplicable) {
                    // Enter comma selection mode with empty Gamma (position 0)
                    ruleEngine.enterCommaSelectionMode($sequentTable, 0);
                }
            });
            
            // Set up dynamic dot visibility for first-point
            if (ruleEngine && ruleEngine.updateFirstPointVisibility) {
                ruleEngine.updateFirstPointVisibility($firstPoint, $ul.closest('table'), options);
            }
            
            // Also trigger immediate refresh for ILL mode to ensure dots show on initial load
            setTimeout(() => {
                let $container = $ul.closest('.proof-container');
                if ($container.length > 0) {
                    refreshILLTensorDotVisibility($container);
                }
            }, 150);
        }
    }

    // Create formula elements
    for (let i = 0; i < sequent[sequentPart].length; i++) {
        let formulaAsJson = sequent[sequentPart][i];
        let $li = $('<li>')
            .data('initialPosition', i)
            .data('formula', formulaAsJson);
        $ul.append($li);

        // Build formula HTML
        let $span = $('<span>', {'class': 'main-formula'})
            .html(createFormulaHTML(formulaAsJson, true));
        if (formulaAsJson['is_cut_formula']) {
            $span.addClass('cut-formula');
            delete formulaAsJson['is_cut_formula'];
        }
        $li.append($span);
        
        // Add comma element
        let $commaSpan = $('<span>', {'class': 'comma'});
        $li.append($commaSpan);

        // Set up interactions using rule engine
        if (ruleEngine && options.withInteraction) {
            ruleEngine.setupFormulaInteraction($li, formulaAsJson, options);
            
            // Only add cut mode to left side (context) in ILL mode
            let isILLMode = ruleEngine.getModeName() === 'intuitionistic';
            if (!isILLMode || sequentPart === 'hyp') {
                addCutOnClick($commaSpan, false);
            }
        }
    }
}

/**
 * Create HTML representation of a formula (mode-agnostic)
 * @param {Object} formulaAsJson - Formula data structure
 * @param {boolean} isMainFormula - Whether this is the main formula (affects styling)
 * @return {string} HTML string representation
 */
function createFormulaHTML(formulaAsJson, isMainFormula = true) {
    switch (formulaAsJson.type) {
        case 'litt':
            return createLittHTML(formulaAsJson.value);

        case 'one':
        case 'bottom':
        case 'top':
        case 'zero':
            let neutralElement = NEUTRAL_ELEMENTS[formulaAsJson.type];
            if (isMainFormula) {
                return `<span class="primaryConnector">${neutralElement}</span>`;
            }
            return neutralElement;

        case 'negation':
            return UNARY_CONNECTORS[formulaAsJson.type] + createFormulaHTML(formulaAsJson.value, false);

        case 'ofcourse':
        case 'whynot':
            let unaryConnector = UNARY_CONNECTORS[formulaAsJson.type];
            let subFormula = createFormulaHTML(formulaAsJson.value, false);
            if (isMainFormula) {
                unaryConnector = `<span class="primaryConnector">${unaryConnector}</span>`;
                subFormula = `<span class="sub-formula">${subFormula}</span>`;
            }
            return unaryConnector + subFormula;

        case 'dual':
            return createFormulaHTML(formulaAsJson.value, false) + '<sup>⊥</sup>';

        case 'implication':
        case 'conjunction':
        case 'disjunction':
        case 'tensor':
        case 'par':
        case 'with':
        case 'plus':
        case 'lollipop':
            let connector = BINARY_CONNECTORS[formulaAsJson.type];
            if (isMainFormula) {
                connector = `<span class="primaryConnector">${connector}</span>`;
            }

            let leftFormula = createFormulaHTML(formulaAsJson['value1'], false);
            let rightFormula = createFormulaHTML(formulaAsJson['value2'], false);
            if (isMainFormula) {
                leftFormula = `<span class="left-formula">${leftFormula}</span>`;
                rightFormula = `<span class="right-formula">${rightFormula}</span>`;
            }
            let formula = leftFormula + connector + rightFormula;

            if (!isMainFormula) {
                return `(${formula})`;
            }

            return formula;

        default:
            console.error('No display rule for type ' + formulaAsJson.type);
            return '';
    }
}

/**
 * Create HTML for literal formula with subscripts
 * @param {string} littName - Literal name
 * @return {string} HTML string with subscripts
 */
function createLittHTML(littName) {
    return littName.replace(/\d+/, digits => `<sub>${digits}</sub>`);
}

/**
 * Get current permutation of formulas in a sequent
 * @param {jQuery} $sequentTable - Sequent table element
 * @return {Object} Permutation object with hyp and cons arrays
 */
function getSequentPermutation($sequentTable) {
    return {
        'hyp': getFormulasPermutation($sequentTable.find('ul.hyp')),
        'cons': getFormulasPermutation($sequentTable.find('ul.cons'))
    };
}

/**
 * Get permutation array for a formula list
 * @param {jQuery} $ul - Formula list element
 * @return {Array} Array of original positions
 */
function getFormulasPermutation($ul) {
    let permutation = [];
    $ul.find('li').each(function(i, obj) {
        let initialPosition = $(obj).data('initialPosition');
        permutation.push(initialPosition);
    });
    return permutation;
}

/**
 * Get identity permutation for a sequent
 * @param {Object} sequent - Sequent data structure
 * @return {Object} Identity permutation object
 */
function getSequentIdentityPermutation(sequent) {
    return {
        'hyp': getFormulaListIdentityPermutation(sequent['hyp'] || []),
        'cons': getFormulaListIdentityPermutation(sequent['cons'] || [])
    };
}

/**
 * Get identity permutation for a formula list
 * @param {Array} formulaList - Array of formulas
 * @return {Array} Identity permutation array
 */
function getFormulaListIdentityPermutation(formulaList) {
    return identity(formulaList.length);
}

/**
 * Create identity array of given length
 * @param {number} n - Length of array
 * @return {Array} Identity array [0, 1, 2, ..., n-1]
 */
function identity(n) {
    return [...Array(n).keys()];
}

/**
 * Apply permutation to sequent
 * @param {Object} sequentWithoutPermutation - Original sequent
 * @param {Object} sequentPermutation - Permutation to apply
 * @return {Object} Permuted sequent
 */
function permuteSequent(sequentWithoutPermutation, sequentPermutation) {
    return {
        'hyp': permute(sequentWithoutPermutation['hyp'], sequentPermutation['hyp']),
        'cons': permute(sequentWithoutPermutation['cons'], sequentPermutation['cons'])
    };
}

/**
 * Apply permutation to formula list
 * @param {Array} formulasWithoutPermutation - Original formula list
 * @param {Array} formulasPermutation - Permutation array
 * @return {Array} Permuted formula list
 */
function permute(formulasWithoutPermutation, formulasPermutation) {
    let newFormulas = [];
    for (let initialPosition of formulasPermutation) {
        newFormulas.push(formulasWithoutPermutation[initialPosition]);
    }
    return newFormulas;
}

/**
 * Check if two formulas are equal (used for axiom rule)
 * @param {Object} formula1 - First formula
 * @param {Object} formula2 - Second formula
 * @return {boolean} True if formulas match
 */
function formulasMatch(formula1, formula2) {
    // For literals, check if the values match
    if (formula1.type === 'litt' && formula2.type === 'litt') {
        return formula1.value === formula2.value;
    }
    
    // For dual formulas, check if the inner values match
    if (formula1.type === 'dual' && formula2.type === 'dual') {
        return formulasMatch(formula1.value, formula2.value);
    }
    
    // Check if types don't match
    if (formula1.type !== formula2.type) {
        return false;
    }
    
    // For complex formulas, could implement deep comparison
    // For now, only handle simple cases
    return false;
}