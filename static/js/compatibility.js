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

// Transformation options symbols (from original code)
const TRANSFORM_OPTIONS = {
    'expand_axiom': '⇫',            // Expand axiom by applying reversible rules
    'expand_axiom_full': '⇯',       // Fully expand axiom (complete proof)
    'eliminate_cut_left': '←',      // Move cut to left premise
    'eliminate_cut_right': '→',     // Move cut to right premise  
    'eliminate_cut_key_case': '↑',  // Eliminate cut at key case
    'eliminate_cut_full': '✄',      // Eliminate all cuts in proof
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
 * Apply transformation to sequent (placeholder)
 * @param {jQuery} $sequentTable - Sequent table
 * @param {Object} transformRequest - Transformation request
 */
function applyTransformation($sequentTable, transformRequest) {
    // This would contain the transformation logic from the original code
    // For now, it's a placeholder
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
 * Remove transform stack (placeholder)
 * @param {jQuery} $container - Container element
 */
function removeTransformStack($container) {
    $container.data('transformStack', null);
    $container.data('transformPointer', null);
}

/**
 * Reload proof with transformation options (placeholder)
 * @param {jQuery} $container - Container element
 * @param {Object} options - Options object
 */
function reloadProofWithTransformationOptions($container, options) {
}

/**
 * Remove transform bar (placeholder)
 * @param {jQuery} $container - Container element
 */
function removeTransformBar($container) {
    $container.find('.transform-bar').remove();
}

// Stub for analytics
if (typeof gtag === 'undefined') {
    function gtag() {
    }
}