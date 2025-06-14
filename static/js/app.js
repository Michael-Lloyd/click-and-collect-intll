// CLICK-AND-COLLECT FRONTEND APPLICATION
// Main JavaScript file that handles UI initialization, sequent parsing, and proof interaction
// Uses jQuery for DOM manipulation and jQuery UI for dialogs and drag-and-drop

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

/* Submit sequent form and start proof construction
   @param element - Form element or child element  
   @param autoSubmit - Whether this is automatic (from URL) or user-initiated
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

/* Parse sequent string and send to backend for validation
   @param sequentAsString - Linear Logic sequent in text format (e.g., "A*B |- A,B")  
   @param $container - jQuery element where proof will be displayed
*/
function parseSequentAsString(sequentAsString, $container) {

    // Check for intuitionistic mode option (experimental feature)
    let options = $container.data('options') || {};
    let intuitionisticMode = options.intuitionisticMode?.value ? '1' : '0';
    
    // Send GET request to backend parser
    $.ajax({
        type: 'GET',
        url: `/parse_sequent/${urlEncode(sequentAsString)}?intuitionisticMode=${intuitionisticMode}`,
        success: function(data)
        {
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

function initMainProof(proofAsJson) {
    cleanMainProof();

    let options = {};

    for (let option of ['withInteraction', 'exportButtons', 'checkProvability']) {
        if (getQueryParamInUrl(option) !== '0') {
            options[option] = true;
        }
    }

    // TODO: Check for problems
    // I've added 'intuitionisticMode' here
    for (let option of ['autoReverse', 'intuitionisticMode', 'cutMode', 'proofTransformation']) {
        if (getQueryParamInUrl(option) !== '0') {
            options[option] = {
                value: getQueryParamInUrl(option) === '1',
                onToggle: onOptionToggle(option)
            };
        }
    }

    if (getQueryParamInUrl('n') !== '0') {
        options.notations = {
            formulasAsString: getQueryPairListParamInUrl('n'),
            onAdd: onNotationAdd,
            onUpdate: onNotationUpdate
        };
    }

    initProof(proofAsJson, $('#main-proof-container'), options);
}

function cleanMainProof() {
    $('#main-proof-container').html('');
}

// ********
// TUTORIAL
// ********

function showTutorial() {
    cleanUrlParams('Show tutorial');

    let $tutorial = $('.tutorial');
    if ($tutorial.data('init') !== true) {
        // Create tutorial proof
        $('.tutorial .proof-container').each(function (i, container) {
            let $container = $(container);
            let proof = JSON.parse(uncompressJson($container.html()));
            $container.html('');
            initProof(proof, $container, {
                withInteraction: true
            });
        })

        $tutorial.data('init', true);
    }

    $tutorial.removeClass('hidden');
}

function hideTutorial() {
    $('.tutorial').addClass('hidden');
    cleanUrlHash('Hide tutorial');
}

// *****
// RULES
// *****

function showRules() {
    cleanUrlParams('Show rules');

    let $rules = $('.rules');
    if ($rules.data('init') !== true) {
        // Create rules proof
        $('.rules .proof-container').each(function (i, container) {
            let $container = $(container);
            let proofAsJson = JSON.parse(uncompressJson($container.html()));
            $container.html('');
            initProof(proofAsJson, $container);
        })

        $rules.data('init', true);
    }
    $rules.removeClass('hidden');
}

function hideRules() {
    $('.rules').addClass('hidden');
    cleanUrlHash('Hide rules');
}

// *********
// ILL RULES
// *********

function showILLRules() {
    cleanUrlParams('Show ILL rules');

    let $illRules = $('.ill-rules');
    if ($illRules.data('init') !== true) {
        // Create ILL rules proof
        $('.ill-rules .proof-container').each(function (i, container) {
            let $container = $(container);
            let proofAsJson = JSON.parse(uncompressJson($container.html()));
            $container.html('');
            initProof(proofAsJson, $container);
        })

        $illRules.data('init', true);
    }
    $illRules.removeClass('hidden');
}

function hideILLRules() {
    $('.ill-rules').addClass('hidden');
    cleanUrlHash('Hide ILL rules');
}

// *******
// OPTIONS
// *******

function onOptionToggle(param) {
    return function (value) {
        if (value) {
            addQueryParamInUrl(param, '1', `${param} set to true`);
        } else {
            addQueryParamInUrl(param, null, `${param} set to false`);
        }
    }
}

function onNotationAdd(notation) {
    addQueryPairInUrl('n', notation, 'Add notation');
}

function onNotationUpdate(notationFormulasAsString) {
    addQueryParamInUrl('n', null, 'Remove all notations');
    for (let notation of notationFormulasAsString) {
        addQueryPairInUrl('n', notation, 'Add notation');
    }
}

// ****************
// UNCOMPRESS PROOF
// ****************

function uncompressProof(compressedProof, $container) {
    $.ajax({
        type: 'POST',
        url: '/uncompress_proof',
        contentType:'application/json; charset=utf-8',
        data: JSON.stringify({ compressedProof }),
        success: function(data)
        {
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

function getQueryParamInUrl (key) {
    let searchParams = new URLSearchParams(window.location.search);
    if (searchParams.has(key)) {
        return searchParams.get(key);
    }

    return null;
}

function addQueryPairInUrl (key, pair, title) {
    let currentUrl = new URL(window.location.href);

    currentUrl.searchParams.append(key, pair);
    currentUrl.hash = '';
    window.history.pushState(pair, title, currentUrl.toString());
}

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

function cleanUrlHash (title) {
    let currentUrl = new URL(window.location.href);

    currentUrl.hash = '';
    window.history.pushState(null, title, currentUrl.toString());
}

function cleanUrlParams (title) {
    let currentUrl = new URL(window.location.href);

    currentUrl.searchParams.forEach(function (value, key) {
        currentUrl.searchParams.delete(key);
    })

    window.history.pushState(null, title, currentUrl.toString());
}

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
