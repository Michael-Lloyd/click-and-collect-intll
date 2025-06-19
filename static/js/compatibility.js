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
    let $container = $sequentTable.closest('.proof-container');
    let options = $container.data('options');

    // Get the proof data from the sequent table
    let proof = recGetProofAsJson($sequentTable);
    let notations = getNotations($container);
    
    // Prepare the transformation request
    let requestData = {
        proof: proof,
        notations: notations,
        transformRequest: transformRequest
    };

    $.ajax({
        type: 'POST',
        url: '/apply_transformation',
        contentType: 'application/json; charset=utf-8',
        data: compressJson(JSON.stringify(requestData)),
        success: function(data) {
            clearSavedProof();
            cleanPedagogicMessage($container);
            
            // Remove the current sequent table and rebuild
            let $sequentContainer = removeSequentTable($sequentTable);
            
            // Temporarily disable transformation mode to rebuild proof
            let wasTransformationMode = options.proofTransformation?.value || false;
            if (options.proofTransformation) {
                options.proofTransformation.value = false;
            }
            
            // Get the rule engine from container
            let ruleEngine = $container.data('ruleEngine');
            
            // Rebuild the proof
            createSubProof(data['proof'], $sequentContainer, options, ruleEngine);
            
            // Re-enable transformation mode and reload with options
            if (wasTransformationMode && options.proofTransformation) {
                options.proofTransformation.value = true;
                reloadProofWithTransformationOptions($container, options);
            }
        },
        error: function(jqXHR, textStatus, errorThrown) {
            if (jqXHR.responseJSON && jqXHR.responseJSON.error_message) {
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
        
        // Refresh comma visibility for last comma spans in the context
        $sequentTable.find('.hyp li:last-child span.comma').each(function() {
            let $commaSpan = $(this);
            updateDotVisibility($commaSpan, shouldShowDots, isCutModeEnabled);
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
        // Store original content if not already stored
        if (!$element.data('original-content')) {
            $element.data('original-content', $element.html());
        }
        
        // Set appropriate class and title
        if (isCutMode) {
            $element.addClass('cut-applicable');
            $element.attr('title', 'Click to apply cut rule');
        } else {
            $element.addClass('tensor-applicable');
            $element.attr('title', 'Click to select context split for tensor rule');
        }
        
        // Replace content with just the dot
        $element.html('.');
    } else {
        // Remove classes and titles
        $element.removeClass('tensor-applicable cut-applicable');
        $element.removeAttr('title');
        
        // Restore original content
        let originalContent = $element.data('original-content');
        if (originalContent !== undefined) {
            $element.html(originalContent);
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
    // Get the current proof stored in the container
    let proof = getProofAsJson($container);
    let notations = getNotations($container);

    $.ajax({
        type: 'POST',
        url: '/get_proof_transformation_options',
        contentType: 'application/json; charset=utf-8',
        data: compressJson(JSON.stringify({ proof, notations })),
        success: function(data) {
            // Disable interaction mode for transformation mode
            options.withInteraction = false;
            
            // Reload the proof with transformation options
            reloadProof($container, data['proofWithTransformationOptions'], options);
            
            // Add to transformation stack for undo/redo
            stackProofTransformation($container);
        },
        error: onAjaxError
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