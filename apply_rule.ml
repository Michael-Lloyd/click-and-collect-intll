(* RULE APPLICATION MODULE
   
   Handles applying Linear Logic inference rules to sequents.
   This is the core logic for interactive proof construction -
   when users click on formulas in the UI, this module determines
   what rule to apply and constructs the resulting proof tree.
*)

(* Apply a rule to a sequent, handling all exceptions internally.
   @param request_as_json - JSON containing rule request and sequent data
   @return proof - New proof tree with rule applied
   @raises various exceptions for invalid requests
*)
let apply_rule_with_exceptions request_as_json =
    let rule_request_as_json = Request_utils.get_key request_as_json "ruleRequest" in
    let rule_request = Rule_request.from_json rule_request_as_json in
    let sequent_with_notations = Sequent_with_notations.from_json request_as_json in
    Proof.from_sequent_and_rule_request sequent_with_notations.sequent sequent_with_notations.notations rule_request

(* Main entry point for rule application API endpoint.
   @param request_as_json - JSON from frontend containing rule and sequent data  
   @return (bool * json) - Success flag and either proof or error message
   
   Returns pedagogical errors (user mistakes) as successful responses with error messages,
   and technical errors (malformed requests) as HTTP error responses.
*)
let apply_rule request_as_json =
    try let proof = apply_rule_with_exceptions request_as_json in
        let proof_as_json = Proof.to_json proof in
        true, `Assoc [
            ("success", `Bool true);
            ("proof", proof_as_json)
        ]
    with
        | Request_utils.Bad_request_exception m -> false, `String ("Bad request: " ^ m)
        | Rule_request.Json_exception m -> false, `String ("Bad rule json: " ^ m)
        | Sequent_with_notations.Json_exception m -> false, `String ("Bad sequent with notations: " ^ m)
        | Proof.Rule_exception (is_pedagogic, m) -> if is_pedagogic
            then true, `Assoc [("success", `Bool false); ("errorMessage", `String m)]
            else false, `String m
