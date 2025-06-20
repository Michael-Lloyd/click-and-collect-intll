// COMPATIBILITY LAYER
// Functions and constants that bridge between the original and refactored code
// This file contains stubs and implementations for functions referenced in the refactored modules

// JSON compression abbreviations (from original code)
const ABBREVIATIONS = {
    '"sequent":': '"s":',           // Sequent data
    '"appliedRule":': '"ar":',      // Applied rule information
    '"ruleRequest":': '"rr":',      // Rule application request
    '"premises":': '"p":',          // Premise sequents
    '"rule":': '"r":',              // Rule name
    '"formulaPosition":': '"fp":',  // Position of formula in sequent
    '"type":': '"t":',              // Formula type
    '"value":': '"v":',             // Formula value
    '"value1":': '"v1":',           // Binary formula left value
    '"value2":': '"v2":'            // Binary formula right value
};

// Transformation options symbols and configurations (from original code)
const TRANSFORM_OPTIONS = {
    'expand_axiom': {
        'button': '⇫',
        'title': 'One step axiom expansion',
        'singleClick': 'expand_axiom',
        'doubleClick': null
    },
    'expand_axiom_full': {
        'button': '⇯',
        'title': 'Full axiom expansion',
        'singleClick': 'expand_axiom_full',
        'doubleClick': null
    },
    'eliminate_cut_left': {
        'button': '←',
        'title': 'Eliminate cut or commute it on left hand-side',
        'singleClick': 'eliminate_cut_left',
        'doubleClick': null
    },
    'eliminate_cut_right': {
        'button': '→',
        'title': 'Eliminate cut or commute it on right hand-side',
        'singleClick': 'eliminate_cut_right',
        'doubleClick': null
    },
    'eliminate_cut_key_case': {
        'button': '↑',
        'title': 'Eliminate cut key-case',
        'singleClick': 'eliminate_cut_key_case',
        'doubleClick': null
    },
    'eliminate_cut_full': {
        'button': '✄',
        'title': 'Fully eliminate this cut',
        'singleClick': 'eliminate_cut_full',
        'doubleClick': null
    }
};

// ILL-specific transformation options symbols and configurations
const ILL_TRANSFORM_OPTIONS = {
    'ill_expand_axiom': {
        'button': '⇫',
        'title': 'One step axiom expansion (ILL)',
        'singleClick': 'ill_expand_axiom',
        'doubleClick': null
    },
    'ill_expand_axiom_full': {
        'button': '⇯',
        'title': 'Full axiom expansion (ILL)',
        'singleClick': 'ill_expand_axiom_full',
        'doubleClick': null
    },
    'ill_eliminate_cut_left': {
        'button': '←',
        'title': 'Eliminate cut or commute it on left hand-side (ILL)',
        'singleClick': 'ill_eliminate_cut_left',
        'doubleClick': null
    },
    'ill_eliminate_cut_right': {
        'button': '→',
        'title': 'Eliminate cut or commute it on right hand-side (ILL)',
        'singleClick': 'ill_eliminate_cut_right',
        'doubleClick': null
    },
    'ill_eliminate_cut_key_case': {
        'button': '↑',
        'title': 'Eliminate cut key-case (ILL)',
        'singleClick': 'ill_eliminate_cut_key_case',
        'doubleClick': null
    },
    'ill_eliminate_cut_full': {
        'button': '✄',
        'title': 'Fully eliminate this cut (ILL)',
        'singleClick': 'ill_eliminate_cut_full',
        'doubleClick': null
    },
    'ill_eliminate_all_cuts': {
        'button': '✂',
        'title': 'Eliminate all cuts from proof (ILL)',
        'singleClick': 'ill_eliminate_all_cuts',
        'doubleClick': null
    },
    'ill_simplify': {
        'button': '⚬',
        'title': 'Simplify proof (ILL)',
        'singleClick': 'ill_simplify',
        'doubleClick': null
    }
};

/**
 * Compress JSON by replacing long field names with abbreviations
 * @param {string} json - JSON string to compress
 * @return {string} Compressed JSON string
 */
function compressJson(json) {
    for (let [field, abbreviation] of Object.entries(ABBREVIATIONS)) {
        json = json.replaceAll(field, abbreviation);
    }
    return json;
}

/**
 * Uncompress JSON by replacing abbreviations with full field names
 * @param {string} json - Compressed JSON string
 * @return {string} Uncompressed JSON string
 */
function uncompressJson(json) {
    for (let [field, abbreviation] of Object.entries(ABBREVIATIONS)) {
        json = json.replaceAll(abbreviation, field);
    }
    return json;
}

/**
 * Handle AJAX errors
 * @param {Object} jqXHR - jQuery XHR object
 * @param {string} textStatus - Error status text
 * @param {string} errorThrown - Error message
 */
function onAjaxError(jqXHR, textStatus, errorThrown) {

    let alertText = 'Technical error, check browser console for more details.';
    if (jqXHR.responseText === 'Body content is too big') {
        alertText = 'Sorry, your proof exceeds the limit.';
    }
    alert(alertText);
}

/**
 * Get transformation options based on current mode (Classical LL vs ILL)
 * @param {boolean} isIllMode - Whether we're in ILL mode
 * @return {Object} Appropriate transformation options object
 */
function getTransformOptions(isIllMode) {
    let options = isIllMode ? ILL_TRANSFORM_OPTIONS : TRANSFORM_OPTIONS;
    return options;
}

/**
 * Get notations from container options
 * @param {jQuery} $container - Proof container
 * @return {Array} Array of notation formulas
 */
function getNotations($container) {
    let options = $container.data('options');

    if (!options.notations?.formulas) {
        return [];
    }

    return options.notations.formulas;
}

/**
 * Check if notation name exists
 * @param {jQuery} $e - Element to search from
 * @param {string} name - Notation name to check
 * @param {number|null} excludePosition - Position to exclude from search
 * @return {boolean} True if notation exists
 */
function notationNameExists($e, name, excludePosition) {
    let $container = $e.closest('.proof-container');
    let options = $container.data('options');

    if (!options.notations || !options.notations.formulasAsString) {
        return false;
    }

    for (let i = 0; i < options.notations.formulasAsString.length; i++) {
        if (i !== excludePosition && name === options.notations.formulasAsString[i][0]) {
            return true;
        }
    }

    return false;
}

/**
 * Check if sequent table identity permutation
 * @param {Object} sequentPermutation - Permutation object
 * @return {boolean} True if identity permutation
 */
function isIdentitySequentPermutation(sequentPermutation) {
    return isIdentity(sequentPermutation['hyp']) && isIdentity(sequentPermutation['cons']);
}

/**
 * Check if array is identity permutation
 * @param {Array} permutation - Permutation array
 * @return {boolean} True if identity
 */
function isIdentity(permutation) {
    for (let i = 0; i < permutation.length; i++) {
        if (i !== permutation[i]) {
            return false;
        }
    }
    return true;
}

/**
 * Invert a permutation array
 * @param {Array} permutation - Permutation to invert
 * @return {Array} Inverted permutation
 */
function invertPermutation(permutation) {
    let invertedPerm = [];
    for (let i of identity(permutation.length)) {
        invertedPerm.push(permutation.indexOf(i));
    }
    return invertedPerm;
}

/**
 * Create identity permutation array
 * @param {number} length - Length of identity permutation
 * @return {Array} Identity permutation
 */
function identity(length) {
    return Array.from({length}, (_, i) => i);
}

/**
 * Get sequent identity permutation
 * @param {Object} sequent - Sequent object
 * @return {Object} Identity permutation for sequent
 */
function getSequentIdentityPermutation(sequent) {
    return {
        'hyp': identity(sequent.hyp.length),
        'cons': identity(sequent.cons.length)
    };
}

/**
 * Get current permutation from sequent table
 * @param {jQuery} $sequentTable - Sequent table
 * @return {Object} Current permutation
 */
function getSequentPermutation($sequentTable) {
    // For now, return identity permutation
    // In a full implementation, this would track actual permutations
    let sequent = $sequentTable.data('sequentWithoutPermutation');
    if (!sequent) {
        return { 'hyp': [], 'cons': [] };
    }
    return getSequentIdentityPermutation(sequent);
}

/**
 * Permute a sequent according to given permutation
 * @param {Object} sequent - Sequent to permute
 * @param {Object} permutation - Permutation to apply
 * @return {Object} Permuted sequent
 */
function permuteSequent(sequent, permutation) {
    return {
        hyp: permute(sequent.hyp, permutation.hyp),
        cons: permute(sequent.cons, permutation.cons)
    };
}

/**
 * Apply permutation to an array
 * @param {Array} array - Array to permute
 * @param {Array} permutation - Permutation array
 * @return {Array} Permuted array
 */
function permute(array, permutation) {
    return permutation.map(i => array[i]);
}

/**
 * Apply rule to sequent (compatibility function)
 * @param {Object} ruleRequest - Rule application request
 * @param {jQuery} $sequentTable - Sequent table element
 */
function applyRule(ruleRequest, $sequentTable) {
    let $container = $sequentTable.closest('.proof-container');
    let options = $container.data('options');

    // Get sequent data and permutation
    let sequentWithoutPermutation = $sequentTable.data('sequentWithoutPermutation');
    let permutationBeforeRule = getSequentPermutation($sequentTable);
    let sequent = permuteSequent(sequentWithoutPermutation, permutationBeforeRule);

    let notations = getNotations($container);

    // Gather intuitionisticMode value
    let intuitionisticMode = options.intuitionisticMode?.value || false;

    let requestData = { 
        ruleRequest, sequent, notations, intuitionisticMode 
    };

    $.ajax({
        type: 'POST',
        url: '/apply_rule',
        contentType:'application/json; charset=utf-8',
        data: compressJson(JSON.stringify(requestData)),
        success: function(data) {
            if (data.success === true) {
                clearSavedProof();
                cleanPedagogicMessage($container);
                let ruleEngine = $container.data('ruleEngine');
                addPremises($sequentTable, data['proof'], permutationBeforeRule, options, ruleEngine);

                if (!isProved($sequentTable) && options.autoReverse?.value) {
                    autoReverseSequentPremises($sequentTable);
                }
            } else {
                displayPedagogicError(data['errorMessage'], $container);
            }
        },
        error: function(jqXHR, textStatus, errorThrown) {
            onAjaxError(jqXHR, textStatus, errorThrown);
        }
    });
}

/**
 * Clear saved proof from URL
 */
function clearSavedProof() {
    addQueryParamInUrl('p', null, 'Clear saved proof');
}

/**
 * Check sequent provability
 * @param {jQuery} $sequentTable - Sequent table to check
 */
function checkProvability($sequentTable) {
    if ($sequentTable.data('provabilityCheckStatus') === 'pending') {
        $sequentTable.data('provabilityCheckStatus', 'needsRecheck');
        return;
    }

    let sequent = $sequentTable.data('sequentWithoutPermutation');
    let $container = $sequentTable.closest('.proof-container');
    let notations = getNotations($container);

    $sequentTable.data('provabilityCheckStatus', 'pending');

    $.ajax({
        type: 'POST',
        url: '/is_sequent_provable',
        contentType:'application/json; charset=utf-8',
        data: compressJson(JSON.stringify({ sequent, notations })),
        success: function(data) {
            if ($sequentTable.data('provabilityCheckStatus') === 'needsRecheck') {
                checkProvability($sequentTable);
                return;
            }

            $sequentTable.data('provabilityCheckStatus', null);
            if (data['is_provable'] === false) {
                recMarkAsNotProvable($sequentTable);
            } else {
                markAsProvable($sequentTable);
            }
        },
        error: onAjaxError
    });
}

/**
 * Auto-reverse sequent premises (placeholder)
 * @param {jQuery} $sequentTable - Sequent table
 */
function autoReverseSequentPremises($sequentTable) {
    // This would contain the auto-reverse logic from the original code
    // For now, it's a placeholder
}

/**
 * Apply transformation to sequent
 * @param {jQuery} $sequentTable - Sequent table
 * @param {Object} transformRequest - Transformation request
 */
function applyTransformation($sequentTable, transformRequest) {
    console.log('[TRANSFORM-FRONTEND] Starting applyTransformation');
    console.log('[TRANSFORM-FRONTEND] Sequent table:', $sequentTable);
    console.log('[TRANSFORM-FRONTEND] Transform request:', transformRequest);
    
    let $container = $sequentTable.closest('.proof-container');
    let options = $container.data('options');
    
    console.log('[TRANSFORM-FRONTEND] Container:', $container);
    console.log('[TRANSFORM-FRONTEND] Options:', options);

    // Check if we're in ILL mode
    let isIllMode = options.intuitionisticMode?.value || false;
    console.log('[TRANSFORM-FRONTEND] ILL mode detected:', isIllMode);
    
    // Get the proof data from the sequent table
    let proof = recGetProofAsJson($sequentTable);
    let notations = getNotations($container);
    
    console.log('[TRANSFORM-FRONTEND] Extracted proof from sequent:', proof);
    console.log('[TRANSFORM-FRONTEND] Extracted notations:', notations);
    
    // Prepare the transformation request
    let requestData = {
        proof: proof,
        notations: notations,
        transformRequest: transformRequest
    };
    
    console.log('[TRANSFORM-FRONTEND] Prepared request data:', requestData);

    // Use appropriate endpoint based on mode
    let transformationUrl = isIllMode ? '/apply_ill_transformation' : '/apply_transformation';
    console.log('[TRANSFORM-FRONTEND] Using transformation URL:', transformationUrl);
    
    let compressedData = compressJson(JSON.stringify(requestData));
    console.log('[TRANSFORM-FRONTEND] Compressed request data:', compressedData);
    $.ajax({
        type: 'POST',
        url: transformationUrl,
        contentType: 'application/json; charset=utf-8',
        data: compressedData,
        success: function(data) {
            console.log('[TRANSFORM-FRONTEND] AJAX success - received transformation response:', data);
            
            clearSavedProof();
            cleanPedagogicMessage($container);
            
            // Remove the current sequent table and rebuild
            let $sequentContainer = removeSequentTable($sequentTable);
            console.log('[TRANSFORM-FRONTEND] Removed sequent table, container:', $sequentContainer);
            
            // Temporarily disable transformation mode to rebuild proof
            let wasTransformationMode = options.proofTransformation?.value || false;
            console.log('[TRANSFORM-FRONTEND] Was transformation mode enabled:', wasTransformationMode);
            
            if (options.proofTransformation) {
                options.proofTransformation.value = false;
            }
            
            // Get the rule engine from container
            let ruleEngine = $container.data('ruleEngine');
            console.log('[TRANSFORM-FRONTEND] Rule engine:', ruleEngine);
            
            // Rebuild the proof - handle both LL and ILL response formats
            let proofData = data['proof'] || data['illProof'];
            if (!proofData) {
                console.error('[TRANSFORM-FRONTEND ERROR] No proof data found in response:', data);
                return;
            }
            
            console.log('[TRANSFORM-FRONTEND] Extracted proof data for rebuild:', proofData);
            console.log('[TRANSFORM-FRONTEND] Transformation applied field:', data['transformationApplied']);
            
            createSubProof(proofData, $sequentContainer, options, ruleEngine);
            console.log('[TRANSFORM-FRONTEND] Rebuilt proof with transformed data');
            
            // Re-enable transformation mode and reload with options
            if (wasTransformationMode && options.proofTransformation) {
                console.log('[TRANSFORM-FRONTEND] Re-enabling transformation mode');
                options.proofTransformation.value = true;
                reloadProofWithTransformationOptions($container, options);
            }
            
            console.log('[TRANSFORM-FRONTEND] Transformation application completed successfully');
        },
        error: function(jqXHR, textStatus, errorThrown) {
            console.error('[TRANSFORM-FRONTEND ERROR] Transformation failed:', {
                status: jqXHR.status,
                statusText: jqXHR.statusText,
                responseText: jqXHR.responseText,
                responseJSON: jqXHR.responseJSON,
                textStatus: textStatus,
                errorThrown: errorThrown,
                transformationUrl: transformationUrl,
                requestData: compressedData
            });
            
            if (jqXHR.responseJSON && jqXHR.responseJSON.error_message) {
                console.log('[TRANSFORM-FRONTEND] Displaying pedagogic error:', jqXHR.responseJSON.error_message);
                displayPedagogicError(jqXHR.responseJSON.error_message, $container);
            } else {
                onAjaxError(jqXHR, textStatus, errorThrown);
            }
        }
    });
}

/**
 * Create option toggle UI element
 * @param {jQuery} $container - Container for option
 * @param {string} optionName - Name of option
 * @param {string} text - Display text
 * @param {string} dialogId - Help dialog ID
 * @param {Function} onSwitchOn - Callback when switched on
 * @param {Function} onToggle - Toggle callback
 */
function createOption($container, optionName, text, dialogId, onSwitchOn, onToggle) {
    let $input = $('<input type="checkbox">');

    let $optionBar = $('<div>', {'class': 'option-bar'})
        .addClass(optionName)
        .append($('<span>', {'class': 'option-label'}).text(text))
        .append($('<label>', {'class': 'switch'})
            .append($input)
            .append($('<span class="slider"></span>')))
        .append(createInfo(`Learn about ${text} option`, dialogId));

    $container.append($optionBar);

    if (optionName) {
        let options = $container.data('options');
        $input.addClass(optionName);
        $input.prop('checked', options[optionName].value);
        $input.on('change', function() {
            if (this.checked) {
                onSwitchOn();
            }
            let options = $container.data('options');
            options[optionName].value = this.checked;
            $container.data('options', options);

            options[optionName].onToggle(this.checked);
            onToggle($container, this.checked);
        });

        onToggle($container, options[optionName].value);
    }
}

/**
 * Create info button for option help
 * @param {string} title - Tooltip title
 * @param {string} dialogId - Dialog ID to open
 * @return {jQuery} Info span element
 */
function createInfo(title, dialogId) {
    return $('<span>', {'class': 'option-info', 'title': title})
        .text('ⓘ')
        .on('click', function () { $(`#${dialogId}`).dialog('open'); });
}

/**
 * Switch off an option
 * @param {jQuery} $container - Container element
 * @param {string} optionName - Option to switch off
 */
function switchOffOption($container, optionName) {
    let $input = $container.find(`input.${optionName}`);
    if ($input.length && $input.prop('checked')) {
        $input.prop('checked', false).trigger('change');
    }
}

/**
 * Create export bar (placeholder)
 * @param {jQuery} $container - Container for export bar
 */
function createExportBar($container) {
}

/**
 * Create notation bar (placeholder)
 * @param {jQuery} $container - Container for notation bar
 * @param {Function} callback - Callback when done
 */
function createNotationBar($container, callback) {
    if (callback) callback();
}

/**
 * Toggle cut mode
 * @param {jQuery} $container - Container element
 * @param {boolean} cutMode - Whether to enable cut mode
 */
function toggleCutMode($container, cutMode) {
    let $mainDiv = $container.children('div.proof');
    
    if (cutMode) {
        $mainDiv.addClass('cut-mode');
    } else {
        $mainDiv.removeClass('cut-mode');
    }
    
    // Refresh ILL tensor dot visibility when cut mode is toggled
    let ruleEngine = $container.data('ruleEngine');
    
    if (ruleEngine && ruleEngine.getModeName() === 'intuitionistic') {
        refreshILLTensorDotVisibility($container);
    }
}

/**
 * Refresh ILL tensor dot visibility for all sequents in the container
 * @param {jQuery} $container - Container element
 */
function refreshILLTensorDotVisibility($container) {
    let ruleEngine = $container.data('ruleEngine');
    
    if (!ruleEngine || ruleEngine.getModeName() !== 'intuitionistic') {
        return;
    }
    
    let $proofDiv = $container.children('div.proof');
    let isCutModeEnabled = $proofDiv.hasClass('cut-mode');
    
    // Find all sequent tables in the container
    $container.find('table').each(function() {
        let $sequentTable = $(this);
        
        // Check if dots should be shown (tensor applicable OR cut mode enabled)
        let sequent = $sequentTable.data('sequent') || $sequentTable.data('sequentWithoutPermutation');
        
        let tensorApplicable = ruleEngine.isTensorRuleApplicable && ruleEngine.isTensorRuleApplicable($sequentTable);
        
        let hasMultipleFormulas = sequent && sequent.hyp && sequent.hyp.length > 1;
        
        let shouldShowDots = (tensorApplicable && hasMultipleFormulas) || isCutModeEnabled;
        
        // Refresh first-point visibility
        $sequentTable.find('.hyp span.first-point').each(function() {
            let $firstPoint = $(this);
            updateDotVisibility($firstPoint, shouldShowDots, isCutModeEnabled);
        });
        
        // Clean up any leftover end-point elements from previous bug
        $sequentTable.find('span.end-point').remove();
        
        // Handle last comma visibility in cut mode - it should show a dot
        let $contextFormulas = $sequentTable.find('.hyp li');
        
        if ($contextFormulas.length > 0) {
            let $lastFormula = $contextFormulas.last();
            let $lastComma = $lastFormula.find('span.comma');
            
            if ($lastComma.length > 0) {
                // Complex logic: tensor mode vs cut mode for last comma
                if (isCutModeEnabled && shouldShowDots) {
                    // Store original content and show dot
                    if ($lastComma.data('original-content') === undefined) {
                        $lastComma.data('original-content', $lastComma.html());
                    }
                    $lastComma.addClass('cut-applicable');
                    $lastComma.attr('title', 'Click to apply cut rule');
                    $lastComma.html('.');
                } else {
                    // The general comma processing loop below will handle this case
                }
            }
        }
        
        // Ensure ALL commas get proper classes in cut mode
        $sequentTable.find('.hyp li span.comma').each(function(index) {
            let $commaSpan = $(this);
            let $parentLi = $commaSpan.closest('li');
            let isLastFormula = $parentLi.is(':last-child');
            
            if (isCutModeEnabled && shouldShowDots) {
                // In cut mode, ALL commas should be cut-applicable for hover effects
                $commaSpan.addClass('cut-applicable');
                $commaSpan.attr('title', 'Click to apply cut rule');
                
                // Only the last comma shows a dot, others remain empty
                if (isLastFormula) {
                    if ($commaSpan.data('original-content') === undefined) {
                        $commaSpan.data('original-content', $commaSpan.html());
                    }
                    $commaSpan.html('.');
                } else {
                    // Non-last commas remain empty but are still clickable
                    if ($commaSpan.html() === '.') {
                        $commaSpan.html('');
                    }
                }
            } else {
                // Not in cut mode, clean up cut classes
                $commaSpan.removeClass('cut-applicable');
                
                // Handle tensor mode for last comma
                if (isLastFormula && tensorApplicable && hasMultipleFormulas) {
                    // Last comma should have tensor-applicable class and let ILL mode handle the dot
                    if (!$commaSpan.hasClass('tensor-applicable')) {
                        $commaSpan.addClass('tensor-applicable');
                    }
                    // Trigger ILL mode to re-evaluate this comma
                    let ruleEngine = $sequentTable.closest('.proof-container').data('ruleEngine');
                    if (ruleEngine && ruleEngine.updateCommaVisibility) {
                        ruleEngine.updateCommaVisibility($commaSpan, $sequentTable, { withInteraction: true });
                    }
                } else if (tensorApplicable && hasMultipleFormulas) {
                    // In tensor mode, ALL commas should be tensor-applicable for context splitting
                    if (!$commaSpan.hasClass('tensor-applicable')) {
                        $commaSpan.addClass('tensor-applicable');
                    }
                    $commaSpan.attr('title', 'Click to select context split for tensor rule');
                    // Non-last commas remain empty (no dot) but are clickable
                    if ($commaSpan.html() === '.') {
                        let originalContent = $commaSpan.data('original-content');
                        if (originalContent !== undefined) {
                            $commaSpan.html(originalContent);
                        } else {
                            $commaSpan.html('');
                        }
                    }
                } else {
                    $commaSpan.removeClass('tensor-applicable');
                    $commaSpan.removeAttr('title');
                    
                    // Restore original content if it was modified
                    let originalContent = $commaSpan.data('original-content');
                    if (originalContent !== undefined) {
                        $commaSpan.html(originalContent);
                        $commaSpan.removeData('original-content');
                    }
                }
            }
        });
    });
}

/**
 * Update dot visibility for a specific element
 * @param {jQuery} $element - The element to update
 * @param {boolean} shouldShowDots - Whether dots should be visible
 * @param {boolean} isCutMode - Whether cut mode is enabled
 */
function updateDotVisibility($element, shouldShowDots, isCutMode) {
    if (shouldShowDots) {
        // CRITICAL: Check if this is a comma element - commas should NOT become dots!
        if ($element.hasClass('comma')) {
            return; // Exit early - let ill-mode.js handle comma elements
        }
        
        // Additional protection: Skip if ill-mode.js is actively refreshing commas
        let $formulaList = $element.closest('ul.commaList');
        if ($formulaList.length && $formulaList.data('refreshing-commas')) {
            return;
        }
        
        // Store original content only if not already stored
        if ($element.data('original-content') === undefined) {
            $element.data('original-content', $element.html());
        }
        
        // Set appropriate class and title
        if (isCutMode) {
            $element.addClass('cut-applicable');
            $element.attr('title', 'Click to apply cut rule');
            // CRITICAL: Remove tensor-applicable class when switching to cut mode
            $element.removeClass('tensor-applicable');
        } else {
            $element.addClass('tensor-applicable');
            $element.attr('title', 'Click to select context split for tensor rule');
            // CRITICAL: Remove cut-applicable class when switching to tensor mode
            $element.removeClass('cut-applicable');
        }
        
        // Replace content with just the dot (only for non-comma elements)
        $element.html('.');
    } else {
        // Remove classes and titles
        $element.removeClass('tensor-applicable cut-applicable');
        $element.removeAttr('title');
        
        // Restore original content
        let originalContent = $element.data('original-content');
        if (originalContent !== undefined) {
            $element.html(originalContent);
            // Clear the stored original content so it can be stored fresh next time
            $element.removeData('original-content');
        }
    }
}

/**
 * Toggle proof transformation mode
 * @param {jQuery} $container - Container element
 * @param {boolean} proofTransformation - Whether to enable transformation mode
 */
function toggleProofTransformation($container, proofTransformation) {
    let options = $container.data('options');
    let $divProof = $container.children('div.proof');

    if (proofTransformation) {
        $divProof.addClass('proof-transformation');
        options.withInteraction = false;
        removeTransformStack($container);
        createUndoRedoButton($container);
        reloadProofWithTransformationOptions($container, options);
    } else {
        if ($divProof.hasClass('proof-transformation')) {
            $divProof.removeClass('proof-transformation');
            options.withInteraction = true;
            let proof = getProofAsJson($container);
            let $mainSequentTable = $container.find('table').last();
            let $sequentContainer = removeSequentTable($mainSequentTable);
            let ruleEngine = $container.data('ruleEngine');
            createSubProof(proof, $sequentContainer, options, ruleEngine);
            removeTransformBar($container);
            removeUndoRedoButton($container);
        }
    }
}

/**
 * Auto-reverse container
 * @param {jQuery} $container - Container element
 * @param {boolean} autoReverse - Whether to enable auto-reverse
 */
function autoReverseContainer($container, autoReverse) {
    if (autoReverse) {
        let $mainSequentTable = $container.find('table').last();
        autoReverseSequentPremises($mainSequentTable);
    }
}

/**
 * Remove transform stack
 * @param {jQuery} $container - Container element
 */
function removeTransformStack($container) {
    $container.data('transformStack', null);
    $container.data('transformPointer', null);
}

/**
 * Clean pedagogic message from container
 * @param {jQuery} $container - Container element
 */
function cleanPedagogicMessage($container) {
    $container.find('.pedagogic-message').remove();
}

/**
 * Display pedagogic error message
 * @param {string} message - Error message to display
 * @param {jQuery} $container - Container element
 */
function displayPedagogicError(message, $container) {
    cleanPedagogicMessage($container);
    let $errorDiv = $('<div>', {'class': 'pedagogic-message error'})
        .text(message);
    $container.prepend($errorDiv);
}

/**
 * Mark proof as incomplete
 * @param {jQuery} $container - Container element
 */
function markAsIncomplete($container) {
    $container.removeClass('complete').addClass('incomplete');
}

/**
 * Mark sequent as provable
 * @param {jQuery} $sequentTable - Sequent table element
 */
function markAsProvable($sequentTable) {
    $sequentTable.data('status', 'provable');
    $sequentTable.find('.turnstile').removeClass('not-provable').addClass('provable');
}

/**
 * Mark sequent as not provable recursively
 * @param {jQuery} $sequentTable - Sequent table element
 */
function recMarkAsNotProvable($sequentTable) {
    $sequentTable.data('status', 'notProvable');
    $sequentTable.find('.turnstile').removeClass('provable').addClass('not-provable');
    markParentSequentsAsNotProvable($sequentTable);
}

/**
 * Mark parent sequents as not provable
 * @param {jQuery} $sequentTable - Sequent table element
 */
function markParentSequentsAsNotProvable($sequentTable) {
    let $parentTable = $sequentTable.nextAll('table').first();
    if ($parentTable.length) {
        recMarkAsNotProvable($parentTable);
    }
}

/**
 * Mark sequent as not auto-provable
 * @param {jQuery} $sequentTable - Sequent table element
 */
function markAsNotAutoProvable($sequentTable) {
    $sequentTable.data('status', 'notAutoProvable');
    $sequentTable.find('.turnstile').removeClass('provable not-provable').addClass('not-auto-provable');
}

/**
 * Check if sequent is proved
 * @param {jQuery} $sequentTable - Sequent table element
 * @return {boolean} True if proved
 */
function isProved($sequentTable) {
    return $sequentTable.data('ruleRequest') !== null && 
           $sequentTable.data('ruleRequest') !== undefined;
}

/**
 * Mark parent sequents as proved
 * @param {jQuery} $sequentTable - Sequent table element
 */
function markParentSequentsAsProved($sequentTable) {
    // Implementation for marking parent sequents as proved
    // This would involve checking if all premises are complete
}

/**
 * Mark parent sequents as provable
 * @param {jQuery} $sequentTable - Sequent table element
 */
function markParentSequentsAsProvable($sequentTable) {
    let $parentTable = $sequentTable.nextAll('table').first();
    if ($parentTable.length) {
        markAsProvable($parentTable);
    }
}

/**
 * Reload proof with transformation options
 * @param {jQuery} $container - Container element
 * @param {Object} options - Options object
 */
function reloadProofWithTransformationOptions($container, options) {
    console.log('[TRANSFORM-FRONTEND] Starting reloadProofWithTransformationOptions');
    console.log('[TRANSFORM-FRONTEND] Container:', $container);
    console.log('[TRANSFORM-FRONTEND] Options:', options);
    
    // Get the current proof stored in the container
    let proof = getProofAsJson($container);
    let notations = getNotations($container);
    
    console.log('[TRANSFORM-FRONTEND] Extracted proof from container:', proof);
    console.log('[TRANSFORM-FRONTEND] Extracted notations:', notations);

    // Check if we're in ILL mode
    let isIllMode = options.intuitionisticMode?.value || false;
    let optionsUrl = isIllMode ? '/get_ill_proof_transformation_options' : '/get_proof_transformation_options';
    
    console.log('[TRANSFORM-FRONTEND] ILL mode detected:', isIllMode);
    console.log('[TRANSFORM-FRONTEND] Using endpoint:', optionsUrl);

    let requestData = { proof, notations };
    let compressedData = compressJson(JSON.stringify(requestData));
    
    console.log('[TRANSFORM-FRONTEND] Request data before compression:', requestData);
    console.log('[TRANSFORM-FRONTEND] Compressed request data:', compressedData);

    $.ajax({
        type: 'POST',
        url: optionsUrl,
        contentType: 'application/json; charset=utf-8',
        data: compressedData,
        success: function(data) {
            console.log('[TRANSFORM-FRONTEND] AJAX success - received response:', data);
            
            // Disable interaction mode for transformation mode
            options.withInteraction = false;
            console.log('[TRANSFORM-FRONTEND] Disabled interaction mode, updated options:', options);
            
            // Use appropriate response field based on mode
            let proofWithOptions = isIllMode ? 
                data['illProofWithTransformationOptions'] : 
                data['proofWithTransformationOptions'];
                
            console.log('[TRANSFORM-FRONTEND] Extracted proof with options:', proofWithOptions);
            console.log('[TRANSFORM-FRONTEND] Available transformation options in proof:', proofWithOptions?.transformOptions);
            
            // Reload the proof with transformation options
            console.log('[TRANSFORM-FRONTEND] Calling reloadProof with proof and options');
            reloadProof($container, proofWithOptions, options);
            
            // Add to transformation stack for undo/redo
            console.log('[TRANSFORM-FRONTEND] Adding to transformation stack');
            stackProofTransformation($container);
            
            console.log('[TRANSFORM-FRONTEND] Transformation options reload completed successfully');
        },
        error: function(jqXHR, textStatus, errorThrown) {
            console.error('[TRANSFORM-FRONTEND ERROR] Failed to get transformation options:', {
                status: jqXHR.status,
                statusText: jqXHR.statusText,
                responseText: jqXHR.responseText,
                responseJSON: jqXHR.responseJSON,
                textStatus: textStatus,
                errorThrown: errorThrown,
                requestUrl: optionsUrl,
                requestData: compressedData
            });
            onAjaxError(jqXHR, textStatus, errorThrown);
        }
    });
}

/**
 * Remove transform bar
 * @param {jQuery} $container - Container element
 */
function removeTransformBar($container) {
    $container.find('.transform-bar').remove();
}

/**
 * Reload proof with new data
 * @param {jQuery} $container - Container element
 * @param {Object} proofAsJson - Proof data
 * @param {Object} options - Options object
 */
function reloadProof($container, proofAsJson, options) {
    let $mainSequentTable = $container.find('table').last();
    let $sequentContainer = removeSequentTable($mainSequentTable);
    let ruleEngine = $container.data('ruleEngine');
    createSubProof(proofAsJson, $sequentContainer, options, ruleEngine);
}

/**
 * Remove sequent table and return its container
 * @param {jQuery} $sequentTable - Sequent table to remove
 * @return {jQuery} Container div where table was located
 */
function removeSequentTable($sequentTable) {
    let $container = $sequentTable.parent();
    $sequentTable.remove();
    return $container;
}

/**
 * Stack current proof for transformation undo/redo
 * @param {jQuery} $container - Container element
 */
function stackProofTransformation($container) {
    let transformStack = $container.data('transformStack') || [];
    let transformPointer = $container.data('transformPointer');
    
    // If we're not at the end of the stack, truncate it
    if (transformPointer !== undefined && transformPointer < transformStack.length - 1) {
        transformStack.length = transformPointer + 1;
    }
    
    // Add current proof to stack
    transformStack.push(getProofAsJson($container));
    $container.data('transformStack', transformStack);

    // Update pointer to the end
    transformPointer = transformStack.length - 1;
    $container.data('transformPointer', transformPointer);

    // Update undo/redo button states
    updateUndoRedoButton($container, transformStack, transformPointer);
}

/**
 * Create undo/redo buttons for transformation mode
 * @param {jQuery} $container - Container element
 */
function createUndoRedoButton($container) {
    let $proof = $container.find('.proof');
    
    // Remove existing buttons first
    $container.find('.undo-redo').remove();
    
    let $redoButton = $('<span>', {class: 'undo-redo redo'})
        .text('↷')
        .attr('title', 'Redo proof transformation')
        .on('click', function() { redoTransformation($container); });
        
    let $undoButton = $('<span>', {class: 'undo-redo undo'})
        .text('↶')
        .attr('title', 'Undo proof transformation')
        .on('click', function() { undoTransformation($container); });
        
    $undoButton.insertAfter($proof);
    $redoButton.insertAfter($proof);
}

/**
 * Remove undo/redo buttons
 * @param {jQuery} $container - Container element
 */
function removeUndoRedoButton($container) {
    $container.find('.undo-redo').remove();
}

/**
 * Update undo/redo button states
 * @param {jQuery} $container - Container element
 * @param {Array} transformStack - Stack of transformations
 * @param {number} transformPointer - Current position in stack
 */
function updateUndoRedoButton($container, transformStack, transformPointer) {
    let $undoButton = $container.find('span.undo');
    let $redoButton = $container.find('span.redo');
    
    // Update undo button
    if (transformStack.length > 0 && transformPointer > 0) {
        $undoButton.addClass('enabled').removeClass('disabled');
    } else {
        $undoButton.addClass('disabled').removeClass('enabled');
    }
    
    // Update redo button
    if (transformStack.length > 0 && transformPointer < transformStack.length - 1) {
        $redoButton.addClass('enabled').removeClass('disabled');
    } else {
        $redoButton.addClass('disabled').removeClass('enabled');
    }
}

/**
 * Undo last transformation
 * @param {jQuery} $container - Container element
 */
function undoTransformation($container) {
    let options = $container.data('options');
    let transformStack = $container.data('transformStack');
    let transformPointer = $container.data('transformPointer');
    
    if (!transformStack || transformPointer <= 0) {
        return; // Nothing to undo
    }
    
    transformPointer = transformPointer - 1;
    $container.data('transformPointer', transformPointer);
    
    reloadProof($container, transformStack[transformPointer], options);
    updateUndoRedoButton($container, transformStack, transformPointer);
}

/**
 * Redo next transformation
 * @param {jQuery} $container - Container element
 */
function redoTransformation($container) {
    let options = $container.data('options');
    let transformStack = $container.data('transformStack');
    let transformPointer = $container.data('transformPointer');
    
    if (!transformStack || transformPointer >= transformStack.length - 1) {
        return; // Nothing to redo
    }
    
    transformPointer = transformPointer + 1;
    $container.data('transformPointer', transformPointer);
    
    reloadProof($container, transformStack[transformPointer], options);
    updateUndoRedoButton($container, transformStack, transformPointer);
}

// Stub for analytics
if (typeof gtag === 'undefined') {
    function gtag() {
    }
}