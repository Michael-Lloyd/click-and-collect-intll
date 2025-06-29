// PROOF CORE MODULE
// Mode-agnostic proof display and management functionality
// Extracted from the original proof.js to separate core logic from mode-specific behavior

/**
 * Initialize a new proof display in the given container
 * @param {Object} proofAsJson - JSON representation of the proof tree
 * @param {jQuery} $container - jQuery element to contain the proof
 * @param {Object} options - Display options (interactions, export buttons, etc.)
 * @param {RuleEngine} ruleEngine - Rule engine for the selected mode
 */
function initProof(proofAsJson, $container, options = {}, ruleEngine = null) {
    // Store options and rule engine for later access by event handlers
    $container.data('options', options);
    $container.data('ruleEngine', ruleEngine);

    // Create main proof display container
    let $proofDiv = $('<div>', {'class': 'proof'});
    $container.append($proofDiv);

    // Apply mode-specific styling
    if (ruleEngine) {
        applyModeStyles($container, ruleEngine.getModeName());
    }

    // If notations are enabled, create notation management UI first
    if (options.notations) {
        createNotationBar($container, function () {
            buildProof(proofAsJson, $container, ruleEngine);
        });
    } else {
        // Build proof directly without notation management
        buildProof(proofAsJson, $container, ruleEngine);
    }
}

/**
 * Build the proof structure and add option controls
 * @param {Object} proofAsJson - JSON representation of the proof tree
 * @param {jQuery} $container - Container element
 * @param {RuleEngine} ruleEngine - Rule engine for the selected mode
 */
function buildProof(proofAsJson, $container, ruleEngine = null) {
    let options = $container.data('options');
    let $proofDiv = $container.children('div.proof');

    createSubProof(proofAsJson, $proofDiv, options, ruleEngine);

    // Add option controls based on available options
    if (options.autoReverse) {
        createOption($container, 'autoReverse', 'Auto-reverse', 'auto-reverse-dialog', function () {
            switchOffOption($container, 'proofTransformation');
        }, autoReverseContainer);
    }

    if (options.intuitionisticMode) {
        createOption($container, 'intuitionisticMode', 'Intuitionistic mode', 'intuitionistic-mode-dialog', function () {
            // Could add mode-specific cleanup here
        }, function($container, intuitionisticMode) {
            let currentRuleEngine = $container.data('ruleEngine');
            toggleIntuitionisticMode($container, intuitionisticMode, currentRuleEngine);
        });
    }

    if (options.cutMode) {
        createOption($container, 'cutMode', 'Cut mode', 'cut-mode-dialog', function () {
            switchOffOption($container, 'proofTransformation');
        }, toggleCutMode);
    }

    if (options.proofTransformation) {
        createOption($container, 'proofTransformation', 'Proof transformation', 'proof-transformation-dialog', function () {
            switchOffOption($container, 'autoReverse');
            switchOffOption($container, 'cutMode');
        }, toggleProofTransformation);
    }

    if (options.exportButtons) {
        createExportBar($container);
    }
}

/**
 * Create a sub-proof display (recursive structure)
 * @param {Object} proofAsJson - JSON representation of the proof
 * @param {jQuery} $subProofDivContainer - Container for the sub-proof
 * @param {Object} options - Display options
 * @param {RuleEngine} ruleEngine - Rule engine for the selected mode
 */
function createSubProof(proofAsJson, $subProofDivContainer, options, ruleEngine = null) {
    let $sequentTable = createSequentTable(proofAsJson.sequent, options, ruleEngine);
    $subProofDivContainer.prepend($sequentTable);

    // Update mode-specific visual elements if needed
    if (ruleEngine && ruleEngine.getModeName() === 'intuitionistic') {
        updateAllCommaVisibility($subProofDivContainer.closest('.proof-container'));
    }

    if (proofAsJson.appliedRule) {
        let permutationBeforeRule = getSequentIdentityPermutation(proofAsJson.sequent);

        if (proofAsJson.appliedRule.ruleRequest.rule === 'exchange') {
            permutationBeforeRule = {
                'hyp': [], 
                'cons': invertPermutation(proofAsJson.appliedRule.ruleRequest.permutation)
            };
            proofAsJson = proofAsJson.appliedRule.premises[0];
        }

        if (proofAsJson.appliedRule) {
            addPremises($sequentTable, proofAsJson, permutationBeforeRule, options, ruleEngine);
            return;
        }
    }

    if (options.checkProvability) {
        checkProvability($sequentTable);
    }
}

/**
 * Create a sequent table element
 * @param {Object} sequent - Sequent data structure
 * @param {Object} options - Display options
 * @param {RuleEngine} ruleEngine - Rule engine for the selected mode
 * @return {jQuery} Sequent table element
 */
function createSequentTable(sequent, options, ruleEngine = null) {
    let $sequentTable = $('<table>')
        .data('sequentWithoutPermutation', sequent);

    let $td = $('<td>');
    $td.append(createSequent(sequent, $sequentTable, options, ruleEngine));
    $sequentTable.append($td);

    let $tagBox = $('<div>', {'class': 'tagBox'})
        .html('&nbsp;');
    $td.append($tagBox);

    return $sequentTable;
}

/**
 * Add premises to a sequent after rule application
 * @param {jQuery} $sequentTable - Sequent table element
 * @param {Object} proofAsJson - Proof data with applied rule
 * @param {Object} permutationBeforeRule - Permutation state before rule
 * @param {Object} options - Display options
 * @param {RuleEngine} ruleEngine - Rule engine for the selected mode
 */
function addPremises($sequentTable, proofAsJson, permutationBeforeRule, options, ruleEngine = null) {
    // Undo previously applied rule if any
    undoRule($sequentTable);

    let ruleRequest = proofAsJson.appliedRule.ruleRequest;

    // Save data
    $sequentTable
        .data('sequentWithPermutation', proofAsJson.sequent)
        .data('permutationBeforeRule', permutationBeforeRule)
        .data('ruleRequest', ruleRequest);
    
    // Update mode-specific visual elements if needed
    if (ruleEngine && ruleEngine.getModeName() === 'intuitionistic') {
        updateAllCommaVisibility($sequentTable.closest('.proof-container'));
    }

    // Add line
    let $td = $sequentTable.find('div.sequent').closest('td');
    let dashedLine = ruleRequest.rule === 'unfold_litt' || ruleRequest.rule === 'unfold_dual';
    $td.addClass(dashedLine ? 'dashed-line' : 'solid-line');

    // Add rule symbol using rule engine
    let ruleSymbol = 'unknown';
    if (ruleEngine) {
        ruleSymbol = ruleEngine.getRuleSymbol(ruleRequest.rule);
    } else {
        // Fallback to basic LL rules
        ruleSymbol = LL_RULES[ruleRequest.rule] || ruleRequest.rule;
    }

    let $ruleSymbol = $('<div>', {'class': 'tag'}).html(ruleSymbol);
    $td.children('.tagBox').addClass(ruleRequest.rule).append($ruleSymbol);
    
    if (options.withInteraction) {
        $ruleSymbol.addClass('clickable');
        $ruleSymbol.on('click', function() {
            clearSavedProof();
            undoRule($sequentTable);
        });
    } else if (options.proofTransformation?.value) {
        let transformDiv = $('<div>', {'class': 'transform'});
        
        // Check if we're in ILL mode to get transformation options from correct location
        let isIllMode = options.intuitionisticMode?.value || false;
        let transformOptions;
        
        if (isIllMode) {
            // ILL mode: transformOptions are at root level of proof object
            transformOptions = proofAsJson.transformOptions;
        } else {
            // LL mode: transformOptions are inside appliedRule
            transformOptions = proofAsJson.appliedRule ? proofAsJson.appliedRule['transformOptions'] : undefined;
        }
        
        $sequentTable.data('transformOptions', transformOptions);
        let activeTransformOptions = getTransformOptions(isIllMode);
        
        // Handle case where transformOptions might be undefined
        if (!transformOptions) {
            return;
        }
        
        console.log('[TRANSFORM-FRONTEND] Processing transformation options:', transformOptions);
        console.log('[TRANSFORM-FRONTEND] Active transform options config:', activeTransformOptions);
        
        for (let transformOption of transformOptions) {
            let transformation = transformOption.transformation;
            let transformConfig = activeTransformOptions[transformation];
            
            console.log('[TRANSFORM-FRONTEND] Processing transform option:', transformOption);
            console.log('[TRANSFORM-FRONTEND] Transform config for', transformation, ':', transformConfig);
            
            if (!transformConfig) {
                // Fallback for unknown transformation types
                transformConfig = {
                    'button': transformation,
                    'title': transformOption.title || transformation,
                    'singleClick': transformation,
                    'doubleClick': null
                };
                console.log('[TRANSFORM-FRONTEND] Using fallback config:', transformConfig);
            }
            
            let $transformSpan = $('<span>', {'class': 'transform-button'})
                .addClass(transformOption.enabled ? 'enabled' : 'disabled')
                .text(transformConfig.button);
            
            console.log('[TRANSFORM-FRONTEND] Created transform button - enabled:', transformOption.enabled, 'button text:', transformConfig.button);
            
            if (transformOption.enabled) {
                $transformSpan.attr('title', transformConfig.title);
                
                if (transformConfig.doubleClick) {
                    // Add both single and double click handlers
                    console.log('[TRANSFORM-FRONTEND] Adding single/double click handlers for:', transformation);
                    addClickAndDoubleClickEvent($transformSpan, function () {
                        console.log('[TRANSFORM-FRONTEND] Single click transform button for:', transformConfig.singleClick);
                        applyTransformation($sequentTable, { transformation: transformConfig.singleClick });
                    }, function () {
                        console.log('[TRANSFORM-FRONTEND] Double click transform button for:', transformConfig.doubleClick);
                        applyTransformation($sequentTable, { transformation: transformConfig.doubleClick });
                    });
                } else {
                    // Single click only
                    console.log('[TRANSFORM-FRONTEND] Adding single click handler for:', transformation);
                    $transformSpan.on('click', function () {
                        console.log('[TRANSFORM-FRONTEND] Clicked transform button for:', transformConfig.singleClick);
                        applyTransformation($sequentTable, { transformation: transformConfig.singleClick });
                    });
                }
            } else {
                // Disabled transformations get a title explaining why they're disabled
                $transformSpan.attr('title', transformOption.title || 'Transformation not available');
                console.log('[TRANSFORM-FRONTEND] Created disabled transform button:', transformOption.title);
            }
            
            transformDiv.append($transformSpan);
        }
        $td.children('.tagBox').append(transformDiv);
    }

    // Add premises
    let premises = proofAsJson.appliedRule.premises;
    if (premises.length === 0) {
        if (options.withInteraction) {
            markParentSequentsAsProved($sequentTable);
        }
    } else if (premises.length === 1) {
        createSubProof(premises[0], $sequentTable.parent(), options, ruleEngine);
    } else {
        let $div = $('<div>');
        $div.insertBefore($sequentTable);
        $sequentTable.addClass('binary-rule');

        if (ruleRequest.rule === 'cut' || ruleRequest.rule === 'ill_cut') {
            premises[0].sequent['cons'].slice(-1)[0]['is_cut_formula'] = true;
            premises[1].sequent['cons'][0]['is_cut_formula'] = true;
        }

        for (let premise of premises) {
            let $sibling = $('<div>', {'class': 'sibling'});
            $div.append($sibling);
            createSubProof(premise, $sibling, options, ruleEngine);
        }
    }
}

/**
 * Remove previously applied rule and its premises
 * @param {jQuery} $sequentTable - Sequent table element
 */
function undoRule($sequentTable) {
    if (isProved($sequentTable)) {
        // Mark all conclusions as provable
        markParentSequentsAsProvable($sequentTable);

        // Mark proof as incomplete
        let $container = $sequentTable.closest('.proof-container');
        markAsIncomplete($container);
    }

    // Erase data
    $sequentTable
        .data('sequentWithPermutation', null)
        .data('permutationBeforeRule', null)
        .data('ruleRequest', null)
        .data('provabilityCheckStatus', null)
        .data('transformOptions', null);

    // Remove line
    let $td = $sequentTable.find('div.sequent').closest('td');
    $td.removeClass('solid-line');
    $td.removeClass('dashed-line');

    // Remove rule symbol
    $td.children('.tagBox').html('');

    // Remove premises
    $sequentTable.prevAll().each(function (i, e) {
        e.remove();
    });
    $sequentTable.removeClass('binary-rule');
}

/**
 * Get complete proof as JSON from container
 * @param {jQuery} $container - Proof container element
 * @return {Object} Proof JSON structure
 */
function getProofAsJson($container) {
    let $mainTable = $container
        .children('div.proof')
        .children('table')
        .last();

    return recGetProofAsJson($mainTable);
}

/**
 * Recursively build proof JSON from sequent table
 * @param {jQuery} $sequentTable - Sequent table element
 * @return {Object} Proof JSON structure
 */
function recGetProofAsJson($sequentTable) {
    let sequentWithoutPermutation = $sequentTable.data('sequentWithoutPermutation');
    let ruleRequest = $sequentTable.data('ruleRequest') || null;
    let appliedRule = null;
    
    if (ruleRequest !== null) {
        let $prev = $sequentTable.prev();
        let premises = [];
        if ($prev.length) {
            if ($prev.prop('tagName') === 'TABLE') {
                premises = [recGetProofAsJson($prev)];
            } else {
                $prev.children('div.sibling').each(function (i, sibling) {
                    premises.push(recGetProofAsJson($(sibling).children('table').last()));
                });
            }
        }
        appliedRule = { ruleRequest, premises };

        // Include transformation options if they exist
        if ($sequentTable.data('transformOptions') !== null) {
            appliedRule.transformOptions = $sequentTable.data('transformOptions');
        }

        let permutationBeforeRule = $sequentTable.data('permutationBeforeRule');
        let displayPermutation = getSequentPermutation($sequentTable);
        if (!isIdentitySequentPermutation(permutationBeforeRule)
            || !isIdentitySequentPermutation(displayPermutation)) {
            let sequentWithPermutation = $sequentTable.data('sequentWithPermutation');

            // Permutation asked by API is from premise to conclusion, and we have the other way
            // We need to invert permutation
            let invertedPermutation = invertPermutation(permutationBeforeRule['cons']);

            // Display permutation asked by API is from premise to displayed conclusion
            let permutedDisplayPermutation = permute(invertedPermutation, displayPermutation['cons']);

            appliedRule = {
                ruleRequest: {
                    rule: 'exchange',
                    permutation: invertedPermutation,
                    displayPermutation: permutedDisplayPermutation
                },
                premises: [{sequent: sequentWithPermutation, appliedRule}]
            };
        }
    }

    return { sequent: sequentWithoutPermutation, appliedRule };
}

/**
 * Apply mode-specific styles to the proof container
 * @param {jQuery} $container - Proof container element
 * @param {string} modeName - Name of the logic mode
 */
function applyModeStyles($container, modeName) {
    let $proofDiv = $container.children('div.proof');
    
    // Remove any existing mode classes
    $proofDiv.removeClass('classical-mode intuitionistic-mode');
    
    // Add the appropriate mode class
    if (modeName === 'intuitionistic') {
        $proofDiv.addClass('intuitionistic-mode');
    } else if (modeName === 'classical') {
        $proofDiv.addClass('classical-mode');
    }
}

/**
 * Toggle between LL and ILL modes by switching rule engines
 * @param {jQuery} $container - Proof container element
 * @param {boolean} intuitionisticMode - Whether to enable ILL mode
 * @param {RuleEngine} currentRuleEngine - Current rule engine
 */
function toggleIntuitionisticMode($container, intuitionisticMode, currentRuleEngine) {
    let options = $container.data('options');
    
    // Reset proof completion status when switching modes
    markAsIncomplete($container);
    
    // Create new rule engine for the selected mode
    let newRuleEngine;
    if (intuitionisticMode) {
        newRuleEngine = new ILLRuleEngine();
    } else {
        newRuleEngine = new LLRuleEngine();
    }
    
    // Update stored rule engine
    $container.data('ruleEngine', newRuleEngine);
    
    // Apply mode-specific styling
    applyModeStyles($container, newRuleEngine.getModeName());

    // Get the original sequent string from URL parameters to re-parse it
    let sequentParam = getQueryParamInUrl('s');
    if (sequentParam !== null) {
        // Re-parse the sequent with the new intuitionistic mode setting
        $.ajax({
            type: 'GET',
            url: `/parse_sequent/${urlEncode(sequentParam)}?intuitionisticMode=${intuitionisticMode ? '1' : '0'}`,
            success: function(data) {
                if (data['is_valid']) {
                    // Clear only the proof div, not the entire container
                    let $proofDiv = $container.children('div.proof');
                    $proofDiv.html('');
                    
                    // Rebuild just the proof part, preserving options
                    createSubProof(data['proof'], $proofDiv, options, newRuleEngine);
                } else {
                    // Parse error, show user-friendly error message
                    let $proofDiv = $container.children('div.proof');
                    $proofDiv.html('');
                    displayPedagogicError(data['error_message'], $container);
                }
            },
            error: onAjaxError
        });
    } else {
        // Fallback: Re-initialize the proof with the updated mode if no sequent in URL
        let proof = getProofAsJson($container);
        let $mainSequentTable = $container.find('table').last();
        let $sequentContainer = removeSequentTable($mainSequentTable);

        createSubProof(proof, $sequentContainer, options, newRuleEngine);
    }
}