// USER INTERACTION MODULE
// Generic user interaction handling for Linear Logic proofs
// Extracted from original files to centralize interaction logic

/**
 * Add click and double click event handling with proper timing
 * @param {jQuery} $element - Element to add events to
 * @param {Function} singleClickCallback - Function to call on single click
 * @param {Function} doubleClickCallback - Function to call on double click
 */
function addClickAndDoubleClickEvent($element, singleClickCallback, doubleClickCallback) {
    const CLICK_DELAY = 200;
    let clickCount = 0;
    let clickTimer = null;

    $element.on('click', function () {
        clickCount++;
        if (clickCount === 1) {
            clickTimer = setTimeout(function () {
                singleClickCallback();
                clickCount = 0;
            }, CLICK_DELAY);
        } else {
            clearTimeout(clickTimer);
            doubleClickCallback();
            clickCount = 0;
        }
    });
}

/**
 * Add cut mode click functionality to an element
 * @param {jQuery} $element - Element to add cut click to
 * @param {boolean} isFirst - Whether this is the first position
 */
function addCutOnClick($element, isFirst) {
    $element.on('click', function () {
        let $sequentTable = $element.closest('table');
        let $container = $sequentTable.closest('.proof-container');
        let options = $container.data('options');

        if (options.cutMode?.value) {
            openCutPopup(function (formula) {
                let formulaPosition = 0;
                if (!isFirst) {
                    let $li = $element.closest('li');
                    formulaPosition = $li.parent().children().index($li) + 1;
                }
                let ruleRequest = { rule: 'cut', formula, formulaPosition };
                
                let ruleEngine = $container.data('ruleEngine');
                if (ruleEngine) {
                    ruleEngine.applyRuleToSequent(ruleRequest, $sequentTable);
                } else {
                    // Fallback to original applyRule function
                    applyRule(ruleRequest, $sequentTable);
                }
            });
        }
    });
}

/**
 * Open cut formula input dialog
 * @param {Function} onFormulaSuccessCallback - Callback when formula is parsed successfully
 */
function openCutPopup(onFormulaSuccessCallback) {
    let $cutFormulaDialog = $('#cut-formula-dialog');
    let $textInput = $cutFormulaDialog.find($('input[name=formulaAsString]'));
    $textInput.select();
    
    $cutFormulaDialog.find('input[type=submit]').off('click')
        .on('click', function () {
            let formulaAsString = $textInput.val();
            parseFormulaAsString(formulaAsString, function (formula) {
                $cutFormulaDialog.dialog('close');
                onFormulaSuccessCallback(formula);
            }, $cutFormulaDialog);
        });
    
    $cutFormulaDialog.dialog('open');
}

/**
 * Parse formula string and call callback on success
 * @param {string} formulaAsString - Formula string to parse
 * @param {Function} onFormulaSuccessCallback - Success callback
 * @param {jQuery} $container - Container for error messages
 */
function parseFormulaAsString(formulaAsString, onFormulaSuccessCallback, $container) {
    $.ajax({
        type: 'GET',
        url: `/parse_formula/${urlEncode(formulaAsString)}`,
        success: function(data) {
            if (data['is_valid']) {
                onFormulaSuccessCallback(data['formula']);
            } else {
                displayPedagogicError(data['error_message'], $container);
            }
        },
        error: onAjaxError
    });
}

/**
 * Auto-prove a sequent using the backend solver
 * @param {jQuery} $sequentTable - Sequent table element
 */
function autoProveSequent($sequentTable) {
    if ($sequentTable.data('status') === 'notProvable') {
        // Cannot auto-prove a sequent whose non-provability has been verified
        return;
    }

    let $container = $sequentTable.closest('.proof-container');
    let options = $container.data('options');
    let ruleEngine = $container.data('ruleEngine');

    // Get sequent data
    let sequent = $sequentTable.data('sequentWithoutPermutation');
    let notations = getNotations($container);

    let $turnstile = $sequentTable.find('.turnstile');

    $.ajax({
        type: 'POST',
        url: '/auto_prove_sequent',
        contentType: 'application/json; charset=utf-8',
        data: compressJson(JSON.stringify({sequent, notations})),
        beforeSend: function() {
            $turnstile.addClass('loading');
        },
        complete: function() {
            $turnstile.removeClass('loading');
        },
        success: function(data) {
            if (data.success) {
                clearSavedProof();
                cleanPedagogicMessage($container);
                let $sequentContainer = removeSequentTable($sequentTable);
                createSubProof(data['proof'], $sequentContainer, options, ruleEngine);
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

/**
 * Remove a sequent table and return its container
 * @param {jQuery} $sequentTable - Sequent table to remove
 * @return {jQuery} Container div
 */
function removeSequentTable($sequentTable) {
    undoRule($sequentTable);
    let $div = $sequentTable.closest('div');
    $sequentTable.remove();
    return $div;
}

/**
 * URL encode a string for safe transmission
 * @param {string} s - String to encode
 * @return {string} URL encoded string
 */
function urlEncode(s) {
    return s.replaceAll('?', '%3F')
        .replaceAll('/', '%2F');
}