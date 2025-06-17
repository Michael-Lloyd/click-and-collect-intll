// VISUAL FEEDBACK MODULE
// Visual effects and user feedback for Linear Logic proofs
// Extracted from original files to centralize visual behavior

/**
 * Display a pedagogical error message
 * @param {string} message - Error message to display
 * @param {jQuery} $container - Container to display message in
 */
function displayPedagogicError(message, $container) {
    displayPedagogicMessage(message, $container, 'error');
}

/**
 * Display a pedagogical info message
 * @param {string} message - Info message to display
 * @param {jQuery} $container - Container to display message in
 */
function displayPedagogicInfo(message, $container) {
    displayPedagogicMessage(message, $container, 'info');
}

/**
 * Display a pedagogical message with specified styling
 * @param {string} message - Message to display
 * @param {jQuery} $container - Container to display message in
 * @param {string} className - CSS class for styling ('error', 'info', etc.)
 */
function displayPedagogicMessage(message, $container, className) {
    let $div = $container.children('div.pedagogic-message');
    
    if (!$div.length) {
        $div = $('<div>', {'class': 'pedagogic-message'})
            .addClass(className);
        $div.append($('<div>', {'class': 'message'}));
        
        let $close = $('<div>', {'class': 'close-button'});
        $close.html('✖');
        $close.on('click', function () { 
            cleanPedagogicMessage($container); 
        });
        $div.append($close);

        let $proofDiv = $container.children('div.proof');
        if ($proofDiv.length) {
            $div.insertAfter($proofDiv);
        } else {
            $container.append($div);
        }
    } else {
        $div.removeClass();
        $div.addClass('pedagogic-message');
        $div.addClass(className);
    }
    
    $div.children('div.message').text(message);
}

/**
 * Clean/remove pedagogical messages from container
 * @param {jQuery} $container - Container to clean messages from
 */
function cleanPedagogicMessage($container) {
    $container.children('div.pedagogic-message').remove();
}

/**
 * Mark a sequent table as proved
 * @param {jQuery} $sequentTable - Sequent table to mark
 */
function markAsProved($sequentTable) {
    $sequentTable.data('status', 'proved');
    let $turnstile = $sequentTable.find('span.turnstile');
    $turnstile.removeClass('not-provable not-auto-provable');
    $turnstile.removeAttr('title');
}

/**
 * Mark a sequent table as provable
 * @param {jQuery} $sequentTable - Sequent table to mark
 */
function markAsProvable($sequentTable) {
    $sequentTable.data('status', 'provable');
    let $turnstile = $sequentTable.find('span.turnstile');
    $turnstile.removeClass('not-provable not-auto-provable');
    $turnstile.removeAttr('title');
}

/**
 * Mark a sequent table as not provable
 * @param {jQuery} $sequentTable - Sequent table to mark
 */
function markAsNotProvable($sequentTable) {
    $sequentTable.data('status', 'notProvable');
    let $turnstile = $sequentTable.find('span.turnstile');
    $turnstile.addClass('not-provable');
    $turnstile.removeClass('not-auto-provable');
    $turnstile.attr('title', 'This sequent is not provable');
}

/**
 * Mark a sequent table as not auto-provable
 * @param {jQuery} $sequentTable - Sequent table to mark
 */
function markAsNotAutoProvable($sequentTable) {
    $sequentTable.data('status', 'notAutoProvable');
    let $turnstile = $sequentTable.find('span.turnstile');
    $turnstile.removeClass('not-provable');
    $turnstile.addClass('not-auto-provable');
    $turnstile.attr('title', 'The automatic prover did not make it on this sequent');
}

/**
 * Recursively mark sequents as not provable
 * @param {jQuery} $sequentTable - Starting sequent table
 */
function recMarkAsNotProvable($sequentTable) {
    markAsNotProvable($sequentTable);

    let $parentSequentTable = getParentSequentTable($sequentTable);
    if ($parentSequentTable !== null) {
        let ruleRequest = $parentSequentTable.data('ruleRequest');
        if (isReversible(ruleRequest)) {
            recMarkAsNotProvable($parentSequentTable);
        }
    }
}

/**
 * Check if a rule is reversible
 * @param {Object} ruleRequest - Rule request to check
 * @return {boolean} True if rule is reversible
 */
function isReversible(ruleRequest) {
    if (!ruleRequest) return false;
    
    switch (ruleRequest.rule) {
        case "par":
        case "with":
        case "bottom":
        case "promotion":
            return true;
        default:
            return false;
    }
}

/**
 * Get parent sequent table in proof tree
 * @param {jQuery} $sequentTable - Child sequent table
 * @return {jQuery|null} Parent sequent table or null
 */
function getParentSequentTable($sequentTable) {
    if (!$sequentTable.is(':last-child')) {
        return $sequentTable.next();
    }

    let $div = $sequentTable.closest('div');
    if ($div.hasClass('proof')) {
        return null;
    }

    return $div.parent().next();
}

/**
 * Mark parent sequents as proved recursively
 * @param {jQuery} $sequentTable - Starting sequent table
 */
function markParentSequentsAsProved($sequentTable) {
    markAsProved($sequentTable);

    let $parentSequentTable = getParentSequentTable($sequentTable);
    if ($parentSequentTable !== null) {
        if (isBinary($parentSequentTable)) {
            let $premises = getPremisesSequentTable($parentSequentTable);
            // Check that all premises are proved
            if ($premises === null || !$premises.every(isProved)) {
                return;
            }
        }
        markParentSequentsAsProved($parentSequentTable);
    } else {
        let $container = $sequentTable.closest('.proof-container');
        markAsComplete($container);
    }
}

/**
 * Mark parent sequents as provable recursively
 * @param {jQuery} $sequentTable - Starting sequent table
 */
function markParentSequentsAsProvable($sequentTable) {
    markAsProvable($sequentTable);

    let $parentSequentTable = getParentSequentTable($sequentTable);
    if ($parentSequentTable !== null) {
        markParentSequentsAsProvable($parentSequentTable);
    }
}

/**
 * Check if sequent table represents a binary rule
 * @param {jQuery} $sequentTable - Sequent table to check
 * @return {boolean} True if binary rule
 */
function isBinary($sequentTable) {
    return $sequentTable.hasClass('binary-rule');
}

/**
 * Check if sequent table is proved
 * @param {jQuery} $sequentTable - Sequent table to check
 * @return {boolean} True if proved
 */
function isProved($sequentTable) {
    return $sequentTable.data('status') === 'proved';
}

/**
 * Get premise sequent tables for a rule
 * @param {jQuery} $sequentTable - Parent sequent table
 * @return {Array|null} Array of premise tables or null
 */
function getPremisesSequentTable($sequentTable) {
    let ruleRequest = $sequentTable.data('ruleRequest') || null;
    if (ruleRequest === null) {
        return [];
    }

    let $prev = $sequentTable.prev();

    if ($prev.prop('tagName') === 'TABLE') {
        return [$prev];
    }

    let $premises = [];
    $prev.children('div.sibling').each(function (i, sibling) {
        let $siblingTable = $(sibling).children('table').last();
        $premises = $premises.concat($siblingTable);
    });

    if ($premises.length < 2) {
        // Proof has not been completely set up
        return null;
    }

    return $premises;
}

/**
 * Mark proof container as complete
 * @param {jQuery} $container - Proof container
 */
function markAsComplete($container) {
    let $mainDiv = $container.children('div.proof');
    $mainDiv.addClass('complete');
}

/**
 * Mark proof container as incomplete
 * @param {jQuery} $container - Proof container
 */
function markAsIncomplete($container) {
    let $mainDiv = $container.children('div.proof');
    $mainDiv.removeClass('complete');
}

/**
 * Apply mode-specific CSS styles
 * @param {jQuery} $container - Container to apply styles to
 * @param {string} modeName - Name of the mode ('classical', 'intuitionistic')
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