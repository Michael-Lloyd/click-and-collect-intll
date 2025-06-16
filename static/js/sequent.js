// /static/js/sequent.js

// **************
// DISPLAY CONFIG
// **************

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

// ***************
// DISPLAY SEQUENT
// ***************

function createSequent(sequent, $sequentTable, options) {
    let $sequentDiv = $('<div>', {'class': 'sequent'});

    if ('hyp' in sequent) {
        createFormulaList(sequent, 'hyp', $sequentDiv, options);
    }

    let $thesisSpan = $('<span class="turnstile">⊢</span>');
    if (options.withInteraction) {
        $thesisSpan.addClass('clickable');
        addClickAndDoubleClickEvent($thesisSpan, function () {
            let ruleRequest = { rule: 'axiom' };
            applyRule(ruleRequest, $sequentTable);
        }, function () {
            autoProveSequent($sequentTable);
        });
    }
    $sequentDiv.append($thesisSpan);

    if ('cons' in sequent) {
        createFormulaList(sequent, 'cons', $sequentDiv, options);
    }

    return $sequentDiv;
}

function createFormulaList(sequent, sequentPart, $sequentDiv, options) {
    let $firstPoint = $('<span>', {'class': 'first-point'});
    $sequentDiv.append($firstPoint);

    let $ul = $('<ul>', {'class': ['commaList ' + sequentPart]});
    $sequentDiv.append($ul);

    if (options.withInteraction) {
        $ul.sortable({
            helper : 'clone',
            axis: 'x',
            opacity: 0.2,
            start: function(e, ui){
                ui.placeholder.width(ui.item.width());
            }
        });
        addCutOnClick($firstPoint, true);
    }

    for (let i = 0; i < sequent[sequentPart].length; i++) {
        let formulaAsJson = sequent[sequentPart][i];
        let $li = $('<li>')
            .data('initialPosition', i)
            .data('formula', formulaAsJson);
        $ul.append($li);

        // Build formula
        let $span = $('<span>', {'class': 'main-formula'})
            .html(createFormulaHTML(formulaAsJson, true));
        if (formulaAsJson['is_cut_formula']) {
            $span.addClass('cut-formula');
            delete formulaAsJson['is_cut_formula'];
        }
        $li.append($span);
        let $commaSpan = $('<span>', {'class': 'comma'});
        $li.append($commaSpan);

        // Add events (click, double-click), and classes for hover
        addEventsAndStyle($li, formulaAsJson, options);
        if (options.withInteraction) {
            addCutOnClick($commaSpan, false);
            
            // Add comma click for ILL tensor rule context splitting
            addCommaClickForTensorSplit($commaSpan, $li, options);
        }
    }
}

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
            return createFormulaHTML(formulaAsJson.value, false)
                + '<sup>⊥</sup>';

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

function createLittHTML(littName) {
    return littName.replace(/\d+/, digits => `<sub>${digits}</sub>`);
}

// *****
// RULES
// *****

function getRules(formulaAsJson, options, isLeftSide = false, $li = null) {
    if (options.withInteraction) {
        // Check if we're in ILL mode to determine rule naming
        let isIntuitionisticMode = options.intuitionisticMode?.value || options.forceILLSymbols || false;
        
        // Note: In ILL mode, context formulas with applicable left rules should still be clickable
        // Only disable context formulas that don't have valid left elimination rules
        
        console.log('Formula click disabling check passed, proceeding with normal rules for:', formulaAsJson.type);
        
        switch (formulaAsJson.type) {
            case 'litt':
            case 'dual':
                // In ILL mode, set up click handler but check applicability when clicked
                if (isIntuitionisticMode && $li) {
                    console.log('*** AXIOM SETUP: In ILL mode - setting up axiom rule for:', formulaAsJson, 'on side:', isLeftSide ? 'left' : 'right');
                    return [{'element': 'main-formula', 'onclick': [{'rule': 'axiom_ill', 'needPosition': false}]}];
                }
                return [{'element': 'main-formula', 'onclick': [{'rule': 'axiom', 'needPosition': false}]}];

            case 'tensor':
                if (isIntuitionisticMode) {
                    if (isLeftSide) {
                        // ILL: Left side tensor elimination
                        return [{'element': 'main-formula', 'onclick': [{'rule': 'tensor_left', 'needPosition': true}]}];
                    } else {
                        // ILL: Right side tensor introduction - always allow since tensor rule should be applicable
                        return [{'element': 'main-formula', 'onclick': [{'rule': 'tensor_right', 'needPosition': true}]}];
                    }
                } else {
                    // Standard LL: Simple tensor rule
                    return [{'element': 'main-formula', 'onclick': [{'rule': 'tensor', 'needPosition': true}]}];
                }

            case 'par':
                return [{'element': 'main-formula', 'onclick': [{'rule': formulaAsJson.type, 'needPosition': true}]}];
                
            case 'with':
                if (isIntuitionisticMode) {
                    if (isLeftSide) {
                        // ILL: Left side with elimination (choose left or right sub-formula)
                        return [
                            {'element': 'left-formula', 'onclick': [{'rule': 'with_left_1', 'needPosition': true}]},
                            {'element': 'right-formula', 'onclick': [{'rule': 'with_left_2', 'needPosition': true}]}
                        ];
                    } else {
                        // ILL: Right side with introduction - always allow for goal with formulas
                        return [{'element': 'main-formula', 'onclick': [{'rule': 'with_right', 'needPosition': true}]}];
                    }
                } else {
                    // Standard LL: Simple with rule
                    return [{'element': 'main-formula', 'onclick': [{'rule': 'with', 'needPosition': true}]}];
                }

            case 'plus':
                if (isIntuitionisticMode) {
                    if (isLeftSide) {
                        // ILL: Left side plus elimination
                        return [{'element': 'main-formula', 'onclick': [{'rule': 'plus_left', 'needPosition': true}]}];
                    } else {
                        // ILL: Right side plus introduction (choose left or right sub-formula) - always allow
                        return [
                            {'element': 'left-formula', 'onclick': [{'rule': 'plus_right_1', 'needPosition': true}]},
                            {'element': 'right-formula', 'onclick': [{'rule': 'plus_right_2', 'needPosition': true}]}
                        ];
                    }
                } else {
                    // Standard LL: Simple plus rules
                    if (isLeftSide) {
                        return [{'element': 'main-formula', 'onclick': [{'rule': 'plus_left', 'needPosition': true}]}];
                    } else {
                        return [{'element': 'main-formula', 'onclick': [{'rule': 'plus_right', 'needPosition': true}]}];
                    }
                }

            case 'lollipop':
                if (isIntuitionisticMode) {
                    if (isLeftSide) {
                        // ILL: Left side lollipop elimination (modus ponens)
                        return [{'element': 'main-formula', 'onclick': [{'rule': 'lollipop_left', 'needPosition': true}]}];
                    } else {
                        // ILL: Right side lollipop introduction (implication introduction) - always allow
                        return [{'element': 'main-formula', 'onclick': [{'rule': 'lollipop', 'needPosition': true}]}];
                    }
                } else {
                    // Standard LL: Simple lollipop rule
                    return [{'element': 'main-formula', 'onclick': [{'rule': 'lollipop', 'needPosition': true}]}];
                }

            case 'one':
            case 'zero': // click on zero will display a pedagogic error
                // In ILL mode, only allow one rule on right side if context is empty
                if (isIntuitionisticMode && !isLeftSide && formulaAsJson.type === 'one') {
                    let $sequentTable = $li.closest('table');
                    if (isOneRuleApplicable($sequentTable)) {
                        return [{'element': 'main-formula', 'onclick': [{'rule': formulaAsJson.type, 'needPosition': false}]}];
                    } else {
                        return [];
                    }
                }
                return [{'element': 'main-formula', 'onclick': [{'rule': formulaAsJson.type, 'needPosition': false}]}];

            case 'top':
            case 'bottom':
                // In ILL mode, top rule is always applicable on right side
                if (isIntuitionisticMode && !isLeftSide && formulaAsJson.type === 'top') {
                    return [{'element': 'main-formula', 'onclick': [{'rule': formulaAsJson.type, 'needPosition': true}]}];
                }
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
    } else if (options.proofTransformation?.value) {
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

    return [];
}

function addEventsAndStyle($li, formulaAsJson, options) {
    // Determine which side of the turnstile we're on
    let $formulaList = $li.closest('ul');
    let isLeftSide = $formulaList.hasClass('hyp');
    let rules = getRules(formulaAsJson, options, isLeftSide, $li);

    console.log('addEventsAndStyle called for formula:', formulaAsJson.type, 'isLeftSide:', isLeftSide, 'rules:', rules);

    if (rules.length === 0) {
        console.log('No rules returned, not adding click events');
        return;
    }
    
    console.log('Adding click events for rules:', rules);

    $li.find('span.' + 'main-formula').first().addClass('hoverable');
    for (let ruleEvent of rules) {
        let $spanForEvent = $li.find('span.' + ruleEvent.element).first();

        // Some hover config
        $spanForEvent.addClass('clickable');
        if (ruleEvent.element !== 'main-formula') {
            $spanForEvent.addClass('highlightableExpr');
        }

        // Add click and double click events
        if (ruleEvent.onclick.length === 1) {
            // Single click
            $spanForEvent.on('click', buildApplyRuleCallBack(ruleEvent.onclick[0], $li, options));
        } else {
            // Single click AND Double click event
            let singleClickCallBack = buildApplyRuleCallBack(ruleEvent.onclick[0], $li, options);
            let doubleClickCallBack = buildApplyRuleCallBack(ruleEvent.onclick[1], $li, options);

            addClickAndDoubleClickEvent($spanForEvent, singleClickCallBack, doubleClickCallBack);
        }
    }
}

function buildApplyRuleCallBack(ruleConfig, $li, options) {
    return function() {
        let ruleConfigCopy = JSON.parse(JSON.stringify(ruleConfig)); // deep copy element
        
        // Handle ILL axiom rule with applicability check
        if (ruleConfigCopy.rule === 'axiom_ill') {
            console.log('*** AXIOM CLICK: ILL axiom rule clicked');
            let formula = $li.data('formula');
            let $sequentTable = $li.closest('table');
            let $formulaList = $li.closest('ul');
            let isLeftSide = $formulaList.hasClass('hyp');
            
            // Check if axiom rule is actually applicable now
            if (isAxiomRuleApplicable($sequentTable, formula, isLeftSide)) {
                console.log('*** AXIOM CLICK: Axiom rule is applicable, proceeding');
                ruleConfigCopy.rule = 'axiom'; // Convert to regular axiom rule
            } else {
                console.log('*** AXIOM CLICK: Axiom rule not applicable, aborting');
                return; // Don't apply the rule
            }
        }
        
        if (ruleConfigCopy.rule === 'axiom') {
            let formula = $li.data('formula');

            let atomName = formula['value'];
            if (formula['type'] === 'dual') {
                // {'type': 'dual', 'value': {'type': 'litt', 'value': ... }
                atomName = formula['value']['value']
            }

            if (notationNameExists($li, atomName, null)) {
                ruleConfigCopy.rule = `unfold_${formula['type']}`;
                ruleConfigCopy.needPosition = true;
            }
        }

        let $sequentTable = $li.closest('table');
        let ruleRequest = { rule: ruleConfigCopy.rule };

        // Check if we're in ILL mode to determine if side information is needed
        let $container = $li.closest('.proof-container');
        let containerOptions = $container.data('options');
        let isIntuitionisticMode = containerOptions && containerOptions.intuitionisticMode?.value;
        
        // Only add sequent side information for ILL mode
        if (isIntuitionisticMode) {
            let $formulaList = $li.closest('ul');
            let isLeftSide = $formulaList.hasClass('hyp');
            let sequentSide = isLeftSide ? 'left' : 'right';
            ruleRequest['sequentSide'] = sequentSide;
            
            // Special handling for ILL tensor_right rule: assume empty Gamma
            if (ruleConfigCopy.rule === 'tensor_right' && sequentSide === 'right') {
                ruleRequest['contextSplit'] = [0]; // Empty Gamma, all context goes to Delta
            }
        }

        if (ruleConfigCopy.needPosition) {
            ruleRequest['formulaPosition'] = $li.parent().children().index($li);
        }

        if (options.withInteraction) {
            applyRule(ruleRequest, $sequentTable);
        } else if (options.proofTransformation?.value) {
            applyTransformation($sequentTable, {transformation: ruleConfigCopy.transformation, ruleRequest});
        }
    }
}

// ******************
// DOUBLE CLICK EVENT
// ******************

const CLICK_DELAY = 200;
window.clickCount = 0;
window.clickTimer = null;

function addClickAndDoubleClickEvent ($element, singleClickCallBack, doubleClickCallBack) {
    // https://stackoverflow.com/a/7845282
    $element.on('click', function () {
        clickCount++;
        if (clickCount === 1) {
            window.clickTimer = setTimeout(function () {
                singleClickCallBack();
                window.clickCount = 0;
            }, CLICK_DELAY);
        } else {
            clearTimeout(window.clickTimer);
            doubleClickCallBack();
            window.clickCount = 0;
        }
    })
}

// *******************
// FORMULA PERMUTATION
// *******************

function getSequentPermutation($sequentTable) {
    return {
        'hyp': getFormulasPermutation($sequentTable.find('ul.hyp')),
        'cons': getFormulasPermutation($sequentTable.find('ul.cons'))
    };
}

function getFormulasPermutation($ul) {
    let permutation = [];

    $ul.find('li').each(function(i, obj) {
        let initialPosition = $(obj).data('initialPosition');
        permutation.push(initialPosition);
    })

    return permutation;
}

function getSequentIdentityPermutation(sequent) {
    return {
        'hyp': getFormulaListIdentityPermutation(sequent['hyp'] || []),
        'cons': getFormulaListIdentityPermutation(sequent['cons'] || [])
    };
}

function getFormulaListIdentityPermutation(formulaList) {
    return identity(formulaList.length);
}

function identity(n) {
    return [...Array(n).keys()];
}

function permuteSequent(sequentWithoutPermutation, sequentPermutation) {
    return {
        'hyp': permute(sequentWithoutPermutation['hyp'], sequentPermutation['hyp']),
        'cons': permute(sequentWithoutPermutation['cons'], sequentPermutation['cons'])
    };
}

function permute(formulasWithoutPermutation, formulasPermutation) {
    let newFormulas = [];

    for (let initialPosition of formulasPermutation) {
        newFormulas.push(formulasWithoutPermutation[initialPosition]);
    }

    return newFormulas;
}

// ******************
// AUTO-PROVE SEQUENT
// ******************

function autoProveSequent($sequentTable) {
    if ($sequentTable.data('status') === 'notProvable') {
        // We can not autoProve a sequent whose non-provability has been verified
        return;
    }

    let $container = $sequentTable.closest('.proof-container');
    let options = $container.data('options');

    // Sequent json that was stored in div may have been permuted before rule applying
    let sequent = $sequentTable.data('sequentWithoutPermutation');
    let notations = getNotations($container);

    let $turnstile = $sequentTable.find('.turnstile');

    $.ajax({
        type: 'POST',
        url: '/auto_prove_sequent',
        contentType:'application/json; charset=utf-8',
        data: compressJson(JSON.stringify({sequent, notations})),
        beforeSend: function() {
            $turnstile.addClass('loading');
        },
        complete: function(){
            $turnstile.removeClass('loading');
        },
        success: function(data)
        {
            if (data.success) {
                clearSavedProof();
                cleanPedagogicMessage($container);
                let $sequentContainer = removeSequentTable($sequentTable);
                createSubProof(data['proof'], $sequentContainer, options);
            } else {
                if (data['is_provable']) {
                    markAsNotAutoProvable($sequentTable);
                } else {
                    recMarkAsNotProvable($sequentTable);
                }
            }
        },
        error: onAjaxError
    });
}

// **************
// SEQUENT STATUS
// **************

function markAsProved($sequentTable) {
    $sequentTable.data('status', 'proved');
    let $turnstile = $sequentTable.find('span.turnstile');
    $turnstile.removeClass('not-provable');
    $turnstile.removeClass('not-auto-provable');
    $turnstile.removeAttr('title');
}

function markAsProvable($sequentTable) {
    $sequentTable.data('status', 'provable');
    let $turnstile = $sequentTable.find('span.turnstile');
    $turnstile.removeClass('not-provable');
    $turnstile.removeClass('not-auto-provable');
    $turnstile.removeAttr('title');
}

function markAsNotProvable($sequentTable) {
    $sequentTable.data('status', 'notProvable');
    let $turnstile = $sequentTable.find('span.turnstile');
    $turnstile.addClass('not-provable');
    $turnstile.removeClass('not-auto-provable');
    $turnstile.attr('title', 'This sequent is not provable');
}

function markAsNotAutoProvable($sequentTable) {
    $sequentTable.data('status', 'notAutoProvable');
    let $turnstile = $sequentTable.find('span.turnstile');
    $turnstile.removeClass('not-provable');
    $turnstile.addClass('not-auto-provable');
    $turnstile.attr('title', 'The automatic prover did not make it on this sequent');
}

// **************************
// COMMA SELECTION FOR TENSOR
// **************************

/* Add comma click functionality for ILL tensor rule context splitting.
   Only active when in ILL mode and tensor rule is applicable on the right side.
   @param $commaSpan - The comma span element
   @param $li - The list item containing the formula
   @param options - Display options including intuitionisticMode
*/
function addCommaClickForTensorSplit($commaSpan, $li, options) {
    console.log('Adding comma click handler to comma span');
    console.log('Options passed to function:', options);
    
    // Check if we're in ILL mode using the options passed to the function
    let isIntuitionisticMode = options.intuitionisticMode?.value || options.forceILLSymbols || false;
    
    console.log('Is intuitionistic mode from options:', isIntuitionisticMode);
    
    if (!isIntuitionisticMode) {
        console.log('Not in ILL mode, skipping comma click handler');
        return; // Only available in ILL mode
    }
    
    // Check if this comma is in the context (left side)
    let $formulaList = $li.closest('ul');
    let isLeftSide = $formulaList.hasClass('hyp');
    
    console.log('Is left side (context):', isLeftSide);
    
    if (!isLeftSide) {
        console.log('Not on left side, skipping comma click handler');
        return; // Comma selection only applies to context formulas
    }
    
    // Set up dynamic comma visibility based on tensor rule applicability
    let $sequentTable = $li.closest('table');
    updateCommaVisibility($commaSpan, $sequentTable);
    
    console.log('About to add click handler to comma span');
    
    // Add click handler that checks if tensor rule is applicable
    $commaSpan.on('click', function(e) {
        e.stopPropagation(); // Prevent event bubbling
        
        console.log('Comma clicked!');
        
        // Re-find the sequent table in case DOM has changed
        let $currentSequentTable = $li.closest('table');
        
        // Check if tensor rule is applicable (goal must be A⊗B)
        if (!isTensorRuleApplicable($currentSequentTable)) {
            console.log('Tensor rule not applicable');
            return; // Only available when tensor rule can be applied
        }
        
        console.log('Tensor rule is applicable');
        
        // Get comma position in context
        let $allFormulas = $formulaList.children('li');
        let commaPosition = $allFormulas.index($li) + 1; // Position after this formula
        
        console.log('Comma position:', commaPosition);
        
        // Enter comma selection mode
        enterCommaSelectionMode($currentSequentTable, commaPosition);
    });
}

/* Update comma visibility based on tensor rule applicability.
   @param $commaSpan - The comma span element
   @param $sequentTable - The sequent table element
*/
function updateCommaVisibility($commaSpan, $sequentTable) {
    // Always check for tensor rule applicability dynamically
    setTimeout(function() {
        if (isTensorRuleApplicable($sequentTable)) {
            $commaSpan.addClass('tensor-applicable');
            $commaSpan.attr('title', 'Click to select context split for tensor rule');
        } else {
            $commaSpan.removeClass('tensor-applicable');
            $commaSpan.removeAttr('title');
        }
    }, 100); // Small delay to ensure sequent data is available
}

/* Check if tensor rule is applicable to the current sequent.
   @param $sequentTable - The sequent table element
   @return boolean - True if tensor rule can be applied
*/
function isTensorRuleApplicable($sequentTable) {
    let sequent = $sequentTable.data('sequent') || $sequentTable.data('sequentWithoutPermutation');
    console.log('Checking tensor rule applicability, sequent:', sequent);
    
    if (!sequent || !sequent.cons || sequent.cons.length !== 1) {
        console.log('Sequent invalid or not single conclusion');
        return false;
    }
    
    let goalFormula = sequent.cons[0];
    console.log('Goal formula:', goalFormula);
    let isTensor = goalFormula.type === 'tensor';
    console.log('Is tensor:', isTensor);
    return isTensor;
}

/* Check if axiom rule is applicable to the current sequent.
   @param $sequentTable - The sequent table element
   @param clickedFormula - The formula being clicked (could be context or goal)
   @param isLeftSide - Whether the clicked formula is on the left side (context)
   @return boolean - True if axiom rule can be applied
*/
function isAxiomRuleApplicable($sequentTable, clickedFormula, isLeftSide) {
    let sequent = $sequentTable.data('sequent') || $sequentTable.data('sequentWithoutPermutation');
    console.log('Checking axiom rule applicability, sequent:', sequent, 'clicked:', clickedFormula, 'isLeft:', isLeftSide);
    
    if (!sequent || !sequent.hyp || !sequent.cons || sequent.cons.length !== 1) {
        console.log('Sequent invalid for axiom rule');
        return false;
    }
    
    // Axiom rule requires exactly one context formula
    if (sequent.hyp.length !== 1) {
        console.log('Axiom rule requires exactly one context formula, found:', sequent.hyp.length);
        return false;
    }
    
    let contextFormula = sequent.hyp[0];
    let goalFormula = sequent.cons[0];
    
    // Check if context formula matches goal formula
    let matches = formulasMatch(contextFormula, goalFormula);
    console.log('Context formula:', contextFormula, 'Goal formula:', goalFormula, 'Match:', matches);
    
    // If they match, axiom rule is applicable regardless of which side was clicked
    return matches;
}

/* Check if two formulas match for axiom rule.
   @param formula1 - First formula
   @param formula2 - Second formula  
   @return boolean - True if formulas match
*/
function formulasMatch(formula1, formula2) {
    console.log('Comparing formulas:', formula1, 'vs', formula2);
    
    // For literals, check if the values match
    if (formula1.type === 'litt' && formula2.type === 'litt') {
        let match = formula1.value === formula2.value;
        console.log('Literal comparison:', formula1.value, '===', formula2.value, '→', match);
        return match;
    }
    
    // For dual formulas, check if the inner values match
    if (formula1.type === 'dual' && formula2.type === 'dual') {
        return formulasMatch(formula1.value, formula2.value);
    }
    
    // Check if types don't match
    if (formula1.type !== formula2.type) {
        console.log('Types do not match:', formula1.type, '!==', formula2.type);
        return false;
    }
    
    // Add more complex formula matching as needed
    // For now, only handle simple cases
    console.log('Formula types not handled in matching:', formula1.type);
    return false;
}

/* Check if one rule is applicable to the current sequent.
   @param $sequentTable - The sequent table element
   @return boolean - True if one rule can be applied
*/
function isOneRuleApplicable($sequentTable) {
    let sequent = $sequentTable.data('sequent') || $sequentTable.data('sequentWithoutPermutation');
    console.log('Checking one rule applicability, sequent:', sequent);
    
    if (!sequent || !sequent.hyp || !sequent.cons || sequent.cons.length !== 1) {
        console.log('Sequent invalid for one rule');
        return false;
    }
    
    // One rule requires empty context
    let isEmpty = sequent.hyp.length === 0;
    console.log('Context is empty:', isEmpty);
    
    return isEmpty;
}

/* Enter comma selection mode for tensor rule context splitting.
   @param $sequentTable - The sequent table element
   @param commaPosition - Position where Gamma ends (0-based)
*/
function enterCommaSelectionMode($sequentTable, commaPosition) {
    let $container = $sequentTable.closest('.proof-container');
    
    // Clear any existing selection state
    clearCommaSelectionMode($sequentTable);
    
    // Mark the sequent table as in comma selection mode
    $sequentTable.addClass('comma-selection-mode');
    $sequentTable.data('selectedCommaPosition', commaPosition);
    
    // Highlight the selected range (Gamma)
    highlightGammaRange($sequentTable, commaPosition);
    
    // Add visual feedback message
    displayCommaSelectionMessage($container, commaPosition);
    
    // Apply tensor rule automatically with the selected split
    applyTensorRuleWithSplit($sequentTable, commaPosition);
}

/* Clear comma selection mode and remove all visual indicators.
   @param $sequentTable - The sequent table element
*/
function clearCommaSelectionMode($sequentTable) {
    let $container = $sequentTable.closest('.proof-container');
    
    // Remove mode class and data
    $sequentTable.removeClass('comma-selection-mode');
    $sequentTable.removeData('selectedCommaPosition');
    
    // Clear highlighting
    $sequentTable.find('.formula-gamma, .formula-delta').removeClass('formula-gamma formula-delta');
    
    // Clear any comma selection messages
    $container.find('.comma-selection-message').remove();
}

/* Highlight formulas in Gamma and Delta ranges.
   @param $sequentTable - The sequent table element
   @param commaPosition - Position where Gamma ends
*/
function highlightGammaRange($sequentTable, commaPosition) {
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

/* Display message about comma selection.
   @param $container - The proof container element
   @param commaPosition - Position where Gamma ends
*/
function displayCommaSelectionMessage($container, commaPosition) {
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

/* Apply tensor rule with the specified context split.
   @param $sequentTable - The sequent table element
   @param commaPosition - Position where Gamma ends
*/
function applyTensorRuleWithSplit($sequentTable, commaPosition) {
    let ruleRequest = {
        rule: 'tensor_right',
        sequentSide: 'right',
        contextSplit: [commaPosition]
    };
    
    // Apply the rule
    applyRule(ruleRequest, $sequentTable);
    
    // Clear selection mode after rule application
    clearCommaSelectionMode($sequentTable);
}

/* Update comma visibility for all sequents in a container.
   @param $container - The proof container element
*/
function updateAllCommaVisibility($container) {
    console.log('Updating all comma visibility');
    $container.find('.proof table').each(function() {
        let $sequentTable = $(this);
        
        // Try to get options from container or use default check
        let containerOptions = $container.data('options');
        let isIntuitionisticMode = containerOptions && containerOptions.intuitionisticMode?.value;
        
        // If container options not available, check if proof has intuitionistic class
        if (!isIntuitionisticMode) {
            isIntuitionisticMode = $container.find('.proof').hasClass('intuitionistic-mode');
        }
        
        console.log('Container has ILL mode:', isIntuitionisticMode);
        
        if (isIntuitionisticMode) {
            $sequentTable.find('.hyp li span.comma').each(function() {
                updateCommaVisibility($(this), $sequentTable);
            });
        }
    });
}
