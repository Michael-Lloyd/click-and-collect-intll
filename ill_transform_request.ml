open Ill_sequent
open Ill_rule_request

(* ILL-specific transformation request types.
   These are adapted from classical LL transformations but tailored for ILL's asymmetric sequents.
   ILL has no par (⅋) rules and different cut elimination patterns. *)
type ill_transform_request =
    | ILL_Expand_axiom                           (* One-step axiom expansion *)
    | ILL_Expand_axiom_full                      (* Complete axiom expansion *)  
    | ILL_Eliminate_cut_left                     (* Cut elimination on left premise *)
    | ILL_Eliminate_cut_key_case                 (* Key-case cut elimination *)
    | ILL_Eliminate_cut_right                    (* Cut elimination on right premise *)
    | ILL_Eliminate_cut_full                     (* Fully eliminate this cut *)
    | ILL_Eliminate_all_cuts                     (* Remove all cuts from proof *)
    | ILL_Simplify                               (* General proof simplification *)
    | ILL_Substitute of string * formula         (* Formula substitution *)
    | ILL_Apply_reversible_first of ill_rule_request (* Apply reversible rules first *)

(* Exception for malformed transformation requests *)
exception ILL_Transform_Json_Exception of string

(* Convert JSON to ILL transform request.
   @param transform_request_as_json - JSON object from frontend
   @return ill_transform_request - Parsed transformation request
   @raises ILL_Transform_Json_Exception for invalid requests *)
let from_json transform_request_as_json =
    try 
        let transformation = Request_utils.get_string transform_request_as_json "transformation" in
        match transformation with
            | "ill_expand_axiom" -> ILL_Expand_axiom
            | "ill_expand_axiom_full" -> ILL_Expand_axiom_full
            | "ill_eliminate_cut_left" -> ILL_Eliminate_cut_left
            | "ill_eliminate_cut_key_case" -> ILL_Eliminate_cut_key_case
            | "ill_eliminate_cut_right" -> ILL_Eliminate_cut_right
            | "ill_eliminate_cut_full" -> ILL_Eliminate_cut_full
            | "ill_eliminate_all_cuts" -> ILL_Eliminate_all_cuts
            | "ill_simplify" -> ILL_Simplify
            | "ill_substitute" ->
                let alias = Request_utils.get_string transform_request_as_json "alias" in
                let raw_formula_as_json = Request_utils.get_key transform_request_as_json "formula" in
                let raw_formula = Raw_sequent.json_to_raw_formula raw_formula_as_json in
                let ill_formula = Ill_rule_request.convert_raw_formula_to_ill raw_formula in
                ILL_Substitute (alias, ill_formula)
            | "ill_apply_reversible_first" ->
                let rule_request_as_json = Request_utils.get_key transform_request_as_json "ruleRequest" in
                let ill_rule_request = Ill_rule_request.from_json rule_request_as_json in
                ILL_Apply_reversible_first (ill_rule_request)
            | _ -> raise (ILL_Transform_Json_Exception ("unknown ILL transformation '" ^ transformation ^ "'"))
    with 
    | Request_utils.Bad_request_exception m -> raise (ILL_Transform_Json_Exception ("bad request: " ^ m))
    | Ill_rule_request.ILL_Rule_Json_Exception m -> raise (ILL_Transform_Json_Exception ("bad rule request: " ^ m))

(* Convert ILL transform request to string representation.
   @param transform_req - ILL transformation request
   @return string - String representation for debugging/logging *)
let to_string = function
    | ILL_Expand_axiom -> "ill_expand_axiom"
    | ILL_Expand_axiom_full -> "ill_expand_axiom_full"
    | ILL_Eliminate_cut_left -> "ill_eliminate_cut_left"
    | ILL_Eliminate_cut_key_case -> "ill_eliminate_cut_key_case"
    | ILL_Eliminate_cut_right -> "ill_eliminate_cut_right"
    | ILL_Eliminate_cut_full -> "ill_eliminate_cut_full"
    | ILL_Eliminate_all_cuts -> "ill_eliminate_all_cuts"
    | ILL_Simplify -> "ill_simplify"
    | ILL_Substitute (alias, formula) -> 
        Printf.sprintf "ill_substitute %s ::= %s" alias (Ill_sequent.formula_to_ascii formula)
    | ILL_Apply_reversible_first (rule_request) -> 
        Printf.sprintf "ill_apply_reversible_first %s" (Ill_rule_request.rule_name rule_request.rule)

(* Convert ILL transform request to JSON representation.
   @param transform_req - ILL transformation request  
   @return Yojson.Basic.t - JSON representation for frontend *)
let to_json = function
    | ILL_Expand_axiom -> `Assoc [("transformation", `String "ill_expand_axiom")]
    | ILL_Expand_axiom_full -> `Assoc [("transformation", `String "ill_expand_axiom_full")]
    | ILL_Eliminate_cut_left -> `Assoc [("transformation", `String "ill_eliminate_cut_left")]
    | ILL_Eliminate_cut_key_case -> `Assoc [("transformation", `String "ill_eliminate_cut_key_case")]
    | ILL_Eliminate_cut_right -> `Assoc [("transformation", `String "ill_eliminate_cut_right")]
    | ILL_Eliminate_cut_full -> `Assoc [("transformation", `String "ill_eliminate_cut_full")]
    | ILL_Eliminate_all_cuts -> `Assoc [("transformation", `String "ill_eliminate_all_cuts")]
    | ILL_Simplify -> `Assoc [("transformation", `String "ill_simplify")]
    | ILL_Substitute (alias, formula) ->
        `Assoc [("transformation", `String "ill_substitute");
                ("alias", `String alias);
                ("formula", Raw_sequent.raw_formula_to_json (Ill_rule_request.ill_formula_to_raw formula))]
    | ILL_Apply_reversible_first (rule_request) ->
        `Assoc [("transformation", `String "ill_apply_reversible_first");
                ("ruleRequest", Ill_rule_request.to_json rule_request)]

(* Check if a transformation is applicable to a given ILL proof node.
   @param transform_req - Transformation to check
   @param ill_proof - ILL proof node
   @return bool * string - (applicable, reason) *)
let is_applicable transform_req ill_proof =
    match transform_req with
    | ILL_Expand_axiom ->
        (* Can expand axiom proofs *)
        (match ill_proof with
         | Ill_proof.ILL_Axiom_proof _ -> (true, "Can expand axiom")
         | _ -> (false, "Not an axiom proof"))
    
    | ILL_Expand_axiom_full ->
        (* Can expand axiom proofs fully *)
        (match ill_proof with
         | Ill_proof.ILL_Axiom_proof _ -> (true, "Can fully expand axiom")
         | _ -> (false, "Not an axiom proof"))
    
    | ILL_Eliminate_cut_left | ILL_Eliminate_cut_right | ILL_Eliminate_cut_key_case | ILL_Eliminate_cut_full ->
        (* Can eliminate cuts *)
        (match ill_proof with
         | Ill_proof.ILL_Cut_proof (_, _, _, _, _) -> (true, "Can eliminate cut")
         | _ -> (false, "Not a cut proof"))
    
    | ILL_Eliminate_all_cuts ->
        (* Can eliminate all cuts if any exist in proof tree *)
        (true, "Can attempt to eliminate all cuts")
    
    | ILL_Simplify ->
        (* Can always attempt simplification *)
        (true, "Can simplify proof")
    
    | ILL_Substitute (_, _) ->
        (* Can always attempt substitution *)
        (true, "Can substitute formulas")
    
    | ILL_Apply_reversible_first (_) ->
        (* Can always attempt to apply reversible rules *)
        (true, "Can apply reversible rules first")

(* Get human-readable description of transformation.
   @param transform_req - ILL transformation request
   @return string - Description for UI display *)
let get_description = function
    | ILL_Expand_axiom -> "One step axiom expansion"
    | ILL_Expand_axiom_full -> "Full axiom expansion"
    | ILL_Eliminate_cut_left -> "Eliminate cut on left premise"
    | ILL_Eliminate_cut_key_case -> "Eliminate cut key-case"
    | ILL_Eliminate_cut_right -> "Eliminate cut on right premise"
    | ILL_Eliminate_cut_full -> "Fully eliminate this cut"
    | ILL_Eliminate_all_cuts -> "Eliminate all cuts from proof"
    | ILL_Simplify -> "Simplify proof"
    | ILL_Substitute (alias, _) -> Printf.sprintf "Substitute definition of %s" alias
    | ILL_Apply_reversible_first (_) -> "Apply reversible rules first"

(* Get symbol for transformation button in UI.
   @param transform_req - ILL transformation request
   @return string - Unicode symbol for button *)
let get_symbol = function
    | ILL_Expand_axiom -> "⇫"           (* One step expansion *)
    | ILL_Expand_axiom_full -> "⇯"      (* Full expansion *)
    | ILL_Eliminate_cut_left -> "←"     (* Cut elimination left *)
    | ILL_Eliminate_cut_key_case -> "↑" (* Key case elimination *)
    | ILL_Eliminate_cut_right -> "→"    (* Cut elimination right *)
    | ILL_Eliminate_cut_full -> "✄"     (* Full cut elimination *)
    | ILL_Eliminate_all_cuts -> "✂"     (* Eliminate all cuts *)
    | ILL_Simplify -> "⚬"               (* Simplification *)
    | ILL_Substitute (_, _) -> "≔"      (* Substitution *)
    | ILL_Apply_reversible_first (_) -> "⟲" (* Apply reversible first *)