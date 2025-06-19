// CLICK-AND-COLLECT FRONTEND APPLICATION (REFACTORED)
// Main JavaScript file that handles UI initialization, sequent parsing, and proof interaction
// Refactored to use modular rule engines for clean separation of LL and ILL logic

/* APPLICATION INITIALIZATION
   Sets up event handlers, processes URL parameters, and initializes the interface
*/
$( function() {
    // Prevent default form submission to handle everything with AJAX
    $('form').each(function (i, item) {
        $(item).on('submit', function(e) {
            e.preventDefault(); // avoid to execute the actual submit of the form.
        });
    });

    // Initialize all dialog boxes (help, export options, etc.) as jQuery UI dialogs
    $('.dialog').each(function (i, item) {
        $(item).dialog({autoOpen: false, width: 500});
    })

    // Check URL parameters for sequent and proof data
    // 's' parameter contains the sequent to prove
    // 'p' parameter contains compressed proof data
    let sequentParam = getQueryParamInUrl('s');
    let compressedProofParam = getQueryParamInUrl('p');

    // If URL contains a sequent parameter, auto-populate and submit the form
    if (sequentParam !== null) {
        let $sequentForm = $('#sequent-form');
        $sequentForm.find($('input[name=sequentAsString]')).val(sequentParam);

        // Only auto-submit if no proof is provided (for clean sequent proving)
        if (compressedProofParam === null) {
            submitSequent($sequentForm, true);
        }
    }

    // If URL contains compressed proof data, decompress and display it
    if (compressedProofParam !== null) {
        uncompressProof(compressedProofParam, $('#main-proof-container'));
    }
    
    // Handle URL hash fragments for direct navigation to tutorial/rules sections
    switch (window.location.hash) {
        case '#tutorial':
            showTutorial();
            break;

        case '#rules':
            showRules();
            break;

        case '#ill-rules':
            showILLRules();
            break;
    }
} );

/* SEQUENT FORM HANDLING
   Functions for processing user input of Linear Logic sequents and initializing proofs
*/

/**
 * Submit sequent form and start proof construction
 * @param {jQuery} element - Form element or child element  
 * @param {boolean} autoSubmit - Whether this is automatic (from URL) or user-initiated
 */
function submitSequent(element, autoSubmit = false) {
    let form = $(element).closest('form');
    let sequentAsString = form.find($('input[name=sequentAsString]')).val();

    if (!autoSubmit) {
        clearSavedProof();

        // Update browser URL with sequent parameter for sharing/bookmarking
        addQueryParamInUrl('s', sequentAsString.toString(), 'Linear logic proof start');

        // Reset proof transformation mode when starting new proof
        addQueryParamInUrl('proof_transformation', null, `proof_transformation set to false`);
    }

    // Google Analytics tracking for usage statistics
    gtag('event', 'submit-sequent', {
        'event_category': 'user-action',
        'event_label': autoSubmit ? 'auto-submit' : 'manual-submit',
        'value': sequentAsString
    });

    parseSequentAsString(sequentAsString, $('#main-proof-container'));
}

/**
 * Parse sequent string and send to backend for validation
 * @param {string} sequentAsString - Linear Logic sequent in text format (e.g., "A*B |- A,B")  
 * @param {jQuery} $container - jQuery element where proof will be displayed
 */
function parseSequentAsString(sequentAsString, $container) {
    // Determine which mode to use based on URL parameters
    let intuitionisticMode = getQueryParamInUrl('intuitionisticMode') === '1' ? '1' : '0';
    
    // Send GET request to backend parser
    $.ajax({
        type: 'GET',
        url: `/parse_sequent/${urlEncode(sequentAsString)}?intuitionisticMode=${intuitionisticMode}`,
        success: function(data) {
            if (data['is_valid']) {
                // Sequent parsed successfully, initialize interactive proof
                initMainProof(data['proof']);
            } else {
                // Parse error, show user-friendly error message
                cleanMainProof();
                displayPedagogicError(data['error_message'], $container);
            }
        },
        error: onAjaxError
    });
}

/**
 * Initialize the main proof with appropriate rule engine
 * @param {Object} proofAsJson - Proof data from backend
 */
function initMainProof(proofAsJson) {
    cleanMainProof();

    let options = buildOptions();
    let ruleEngine = createRuleEngine(options);

    initProof(proofAsJson, $('#main-proof-container'), options, ruleEngine);
}

/**
 * Create appropriate rule engine based on options
 * @param {Object} options - Display and interaction options
 * @return {RuleEngine} Appropriate rule engine instance
 */
function createRuleEngine(options) {
    if (options.intuitionisticMode?.value) {
        return new ILLRuleEngine();
    } else {
        return new LLRuleEngine();
    }
}

/**
 * Build options object from URL parameters
 * @return {Object} Options configuration
 */
function buildOptions() {
    let options = {};

    // Standard boolean options
    for (let option of ['withInteraction', 'exportButtons', 'checkProvability']) {
        if (getQueryParamInUrl(option) !== '0') {
            options[option] = true;
        }
    }
    
    // withInteraction should be enabled by default unless explicitly disabled
    if (options.withInteraction === undefined) {
        options.withInteraction = true;
    }

    // Toggle options with callbacks
    for (let option of ['autoReverse', 'intuitionisticMode', 'cutMode', 'proofTransformation']) {
        if (getQueryParamInUrl(option) !== '0') {
            options[option] = {
                value: getQueryParamInUrl(option) === '1',
                onToggle: onOptionToggle(option)
            };
        }
    }

    // Notation options
    if (getQueryParamInUrl('n') !== '0') {
        options.notations = {
            formulasAsString: getQueryPairListParamInUrl('n'),
            onAdd: onNotationAdd,
            onUpdate: onNotationUpdate
        };
    }

    return options;
}

/**
 * Clean the main proof container
 */
function cleanMainProof() {
    $('#main-proof-container').html('');
}

// *********
// TUTORIALS
// *********

/**
 * Show the main LL tutorial
 */
function showTutorial() {
    cleanUrlParams('Show tutorial');

    let $tutorial = $('.tutorial');
    if ($tutorial.data('init') !== true) {
        // Create tutorial proof with LL rule engine
        $('.tutorial .proof-container').each(function (i, container) {
            let $container = $(container);
            let proof = JSON.parse(uncompressJson($container.html()));
            $container.html('');
            let ruleEngine = new LLRuleEngine();
            initProof(proof, $container, {
                withInteraction: true
            }, ruleEngine);
        })

        $tutorial.data('init', true);
    }

    $tutorial.removeClass('hidden');
}

/**
 * Hide the tutorial
 */
function hideTutorial() {
    $('.tutorial').addClass('hidden');
    cleanUrlHash('Hide tutorial');
}

/**
 * Show the LL rules reference
 */
function showRules() {
    cleanUrlParams('Show rules');

    let $rules = $('.rules');
    if ($rules.data('init') !== true) {
        // Create rules proof with LL rule engine
        $('.rules .proof-container').each(function (i, container) {
            let $container = $(container);
            let proofAsJson = JSON.parse(uncompressJson($container.html()));
            $container.html('');
            let ruleEngine = new LLRuleEngine();
            initProof(proofAsJson, $container, {}, ruleEngine);
        })

        $rules.data('init', true);
    }
    $rules.removeClass('hidden');
}

/**
 * Hide the rules reference
 */
function hideRules() {
    $('.rules').addClass('hidden');
    cleanUrlHash('Hide rules');
}

/**
 * Show the ILL rules reference
 */
function showILLRules() {
    cleanUrlParams('Show ILL rules');

    let $illRules = $('.ill-rules');
    if ($illRules.data('init') !== true) {
        // Create ILL rules proof with ILL rule engine
        $('.ill-rules .proof-container').each(function (i, container) {
            let $container = $(container);
            let proofAsJson = JSON.parse(uncompressJson($container.html()));
            $container.html('');
            let ruleEngine = new ILLRuleEngine();
            initProof(proofAsJson, $container, {
                withInteraction: false
            }, ruleEngine);
        })

        $illRules.data('init', true);
    }
    $illRules.removeClass('hidden');
}

/**
 * Hide the ILL rules reference
 */
function hideILLRules() {
    $('.ill-rules').addClass('hidden');
    cleanUrlHash('Hide ILL rules');
}

// *******
// OPTIONS
// *******

/**
 * Create option toggle callback
 * @param {string} param - URL parameter name
 * @return {Function} Toggle callback function
 */
function onOptionToggle(param) {
    return function (value) {
        if (value) {
            addQueryParamInUrl(param, '1', `${param} set to true`);
        } else {
            addQueryParamInUrl(param, null, `${param} set to false`);
        }
    }
}

/**
 * Handle notation addition
 * @param {Array} notation - Notation to add
 */
function onNotationAdd(notation) {
    addQueryPairInUrl('n', notation, 'Add notation');
}

/**
 * Handle notation updates
 * @param {Array} notationFormulasAsString - Updated notations
 */
function onNotationUpdate(notationFormulasAsString) {
    addQueryParamInUrl('n', null, 'Remove all notations');
    for (let notation of notationFormulasAsString) {
        addQueryPairInUrl('n', notation, 'Add notation');
    }
}

// ****************
// UNCOMPRESS PROOF
// ****************

/**
 * Uncompress and display a proof from compressed data
 * @param {string} compressedProof - Compressed proof data
 * @param {jQuery} $container - Container to display proof in
 */
function uncompressProof(compressedProof, $container) {
    $.ajax({
        type: 'POST',
        url: '/uncompress_proof',
        contentType:'application/json; charset=utf-8',
        data: JSON.stringify({ compressedProof }),
        success: function(data) {
            if (data['proof']) {
                initMainProof(data['proof']);
            } else {
                cleanMainProof();
                displayPedagogicError(data['error_message'], $container);
            }
        },
        error: onAjaxError
    });
}

// *****
// UTILS
// *****

/**
 * Add query parameter to URL
 * @param {string} key - Parameter key
 * @param {string|null} value - Parameter value (null to remove)
 * @param {string} title - History title
 */
function addQueryParamInUrl (key, value, title) {
    let currentUrl = new URL(window.location.href);

    if (value !== null) {
        currentUrl.searchParams.set(key, value);
    } else {
        currentUrl.searchParams.delete(key);
    }
    currentUrl.hash = '';
    window.history.pushState(value, title, currentUrl.toString());
}

/**
 * Get query parameter from URL
 * @param {string} key - Parameter key
 * @return {string|null} Parameter value or null
 */
function getQueryParamInUrl (key) {
    let searchParams = new URLSearchParams(window.location.search);
    if (searchParams.has(key)) {
        return searchParams.get(key);
    }

    return null;
}

/**
 * Add query parameter pair to URL (for multiple values)
 * @param {string} key - Parameter key
 * @param {Array} pair - Parameter value pair
 * @param {string} title - History title
 */
function addQueryPairInUrl (key, pair, title) {
    let currentUrl = new URL(window.location.href);

    currentUrl.searchParams.append(key, pair);
    currentUrl.hash = '';
    window.history.pushState(pair, title, currentUrl.toString());
}

/**
 * Get query parameter pair list from URL
 * @param {string} key - Parameter key
 * @return {Array|null} Array of parameter pairs or null
 */
function getQueryPairListParamInUrl (key) {
    let searchParams = new URLSearchParams(window.location.search);
    if (searchParams.has(key)) {
        let pairList = [];

        for (let pair of searchParams.getAll(key)) {
            pairList.push(pair.split(','));
        }

        return pairList;
    }

    return null;
}

/**
 * Clean URL hash
 * @param {string} title - History title
 */
function cleanUrlHash (title) {
    let currentUrl = new URL(window.location.href);

    currentUrl.hash = '';
    window.history.pushState(null, title, currentUrl.toString());
}

/**
 * Clean URL parameters
 * @param {string} title - History title
 */
function cleanUrlParams (title) {
    let currentUrl = new URL(window.location.href);

    currentUrl.searchParams.forEach(function (value, key) {
        currentUrl.searchParams.delete(key);
    })

    window.history.pushState(null, title, currentUrl.toString());
}

/**
 * Copy current URL to clipboard
 */
function copyUrlToClipboard () {
    // https://stackoverflow.com/questions/49618618/copy-current-url-to-clipboard/49618964#49618964

    let dummy = document.createElement('input'),
        text = window.location.href;

    document.body.appendChild(dummy);
    dummy.value = text;
    dummy.select();
    document.execCommand('copy');
    document.body.removeChild(dummy);
}