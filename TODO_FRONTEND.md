You need to ensure all AJAX requests (that might care about proof rules) include this option when appropriate.
The main calls are:

    /apply_rule

    /parse_sequent/...

    /is_sequent_provable

    /auto_reverse_sequent
