(* INTUITIONISTIC LINEAR LOGIC SEQUENT PARSING MODULE
   
   This module provides safe parsing of ILL sequents from string input.
   It handles the conversion from user text input to internal ILL data structures.
   
   Key differences from classical LL parsing:
   - ILL sequents have the form Γ ⊢ A (single conclusion)
   - Different connective set (no ⅋, &, !, ?)
   - Added linear implication A ⊸ B
   - Error messages tailored for ILL syntax
   
   The parser reuses the existing lexer/parser infrastructure but processes
   the results differently for ILL semantics.
*)

open Ill_sequent
open Ill_proof

(* CONVERSION FROM RAW SEQUENT TO ILL *)

(* Exception for invalid ILL connectives *)
exception Invalid_ILL_Connective of string;;

(* Exception for invalid ILL sequent structure *)
exception Invalid_ILL_Sequent_Structure of string;;

(* Convert raw parsed sequent to ILL sequent structure.
   @param raw_seq - Raw sequent from parser
   @return ill_sequent - Converted ILL sequent
   @raises Invalid_ILL_Sequent_Structure if not valid ILL sequent
*)
let rec convert_raw_to_ill_sequent raw_seq =
    (* Convert raw formulas to ILL formulas *)
    let context_formulas = List.map convert_raw_formula_to_ill raw_seq.Raw_sequent.hyp in
    let conclusion_formulas = List.map convert_raw_formula_to_ill raw_seq.Raw_sequent.cons in
    
    (* ILL requires exactly one conclusion *)
    match conclusion_formulas with
    | [] ->
        raise (Invalid_ILL_Sequent_Structure "ILL sequent must have exactly one conclusion")
    | [goal] ->
        { context = context_formulas; goal = goal }
    | _ ->
        raise (Invalid_ILL_Sequent_Structure "ILL sequent can have only one conclusion formula")

(* Convert raw formula to ILL formula.
   @param raw_formula - Raw formula from parser
   @return formula - ILL formula
   @raises Invalid_ILL_Connective if formula uses non-ILL connectives
*)
and convert_raw_formula_to_ill = function
    | Raw_sequent.One -> One
    | Raw_sequent.Top -> Top
    | Raw_sequent.Litt s -> Litt s
    | Raw_sequent.Tensor (f1, f2) -> 
        Tensor (convert_raw_formula_to_ill f1, convert_raw_formula_to_ill f2)
    | Raw_sequent.Plus (f1, f2) -> 
        Plus (convert_raw_formula_to_ill f1, convert_raw_formula_to_ill f2)
    | Raw_sequent.Lollipop (f1, f2) ->
        Lollipop (convert_raw_formula_to_ill f1, convert_raw_formula_to_ill f2)
    
    (* Invalid connectives for ILL *)
    | Raw_sequent.Bottom -> 
        raise (Invalid_ILL_Connective "⊥ (bottom)")
    | Raw_sequent.Zero -> 
        raise (Invalid_ILL_Connective "0 (zero)")
    | Raw_sequent.Dual _ -> 
        raise (Invalid_ILL_Connective "^ (dual)")
    | Raw_sequent.Par (_, _) -> 
        raise (Invalid_ILL_Connective "⅋ (par)")
    | Raw_sequent.With (_, _) -> 
        raise (Invalid_ILL_Connective "& (with)")
    | Raw_sequent.Ofcourse _ -> 
        raise (Invalid_ILL_Connective "! (of course)")
    | Raw_sequent.Whynot _ -> 
        raise (Invalid_ILL_Connective "? (why not)")

(* VALIDATION *)

(* Validate that an ILL formula only uses valid ILL connectives.
   @param formula - ILL formula to validate
   @raises Invalid_ILL_Connective if invalid connectives found
*)
let rec validate_ill_formula = function
    | One | Top | Litt _ -> ()
    | Tensor (f1, f2) | Plus (f1, f2) | Lollipop (f1, f2) ->
        validate_ill_formula f1;
        validate_ill_formula f2

(* Validate that an ILL sequent only uses valid ILL connectives.
   @param ill_seq - ILL sequent to validate
   @raises Invalid_ILL_Connective if invalid connectives found
*)
let validate_ill_sequent ill_seq =
    List.iter validate_ill_formula ill_seq.context;
    validate_ill_formula ill_seq.goal

(* JSON SERIALIZATION *)

(* Convert ILL formula to JSON representation.
   @param formula - ILL formula
   @return Yojson.Basic.t - JSON representation
*)
let rec ill_formula_to_json = function
    | One -> `Assoc [("t", `String "one")]
    | Top -> `Assoc [("t", `String "top")]
    | Litt s -> `Assoc [("t", `String "litt"); ("v", `String s)]
    | Tensor (f1, f2) -> `Assoc [
        ("t", `String "tensor");
        ("v1", ill_formula_to_json f1);
        ("v2", ill_formula_to_json f2)
    ]
    | Plus (f1, f2) -> `Assoc [
        ("t", `String "plus");
        ("v1", ill_formula_to_json f1);
        ("v2", ill_formula_to_json f2)
    ]
    | Lollipop (f1, f2) -> `Assoc [
        ("t", `String "lollipop");
        ("v1", ill_formula_to_json f1);
        ("v2", ill_formula_to_json f2)
    ]

(* Convert ILL sequent to JSON representation.
   @param ill_seq - ILL sequent
   @return Yojson.Basic.t - JSON representation
*)
let ill_sequent_to_json ill_seq =
    `Assoc [
        ("context", `List (List.map ill_formula_to_json ill_seq.context));
        ("goal", ill_formula_to_json ill_seq.goal)
    ]

(* SAFE PARSING WITH ERROR HANDLING *)

(* Parse an ILL sequent string with comprehensive error handling.
   Returns JSON response suitable for the frontend API.
   @param sequent_string - User input string (e.g., "A, B |- A*B")
   @return Yojson.Basic.t - JSON with success/failure and proof/error
*)
let safe_parse sequent_string =
    try
        (* Use existing LL parser to get raw formula structure *)
        let raw_sequent = Ll_parser.main Ll_lexer.token (Lexing.from_string sequent_string) in
        
        (* Convert raw sequent to ILL sequent format *)
        let ill_sequent = convert_raw_to_ill_sequent raw_sequent in
        
        (* Validate that sequent uses only ILL connectives *)
        validate_ill_sequent ill_sequent;
        
        (* Create initial hypothesis proof *)
        let initial_proof = ILL_Hypothesis_proof ill_sequent in
        
        (* Return success response *)
        `Assoc [
            ("is_valid", `Bool true);
            ("proof", to_json initial_proof);
            ("sequent", ill_sequent_to_json ill_sequent)
        ]
    with
    | Parsing.Parse_error ->
        `Assoc [
            ("is_valid", `Bool false);
            ("error_message", `String "Syntax error: please check ILL syntax rules")
        ]
    | Failure msg when msg = "lexing: empty token" ->
        `Assoc [
            ("is_valid", `Bool false);
            ("error_message", `String "Empty input: please enter an ILL sequent")
        ]
    | Invalid_ILL_Connective conn ->
        `Assoc [
            ("is_valid", `Bool false);
            ("error_message", `String ("Invalid ILL connective: " ^ conn ^ ". ILL supports: *, +, -o, 1, T"))
        ]
    | Invalid_ILL_Sequent_Structure msg ->
        `Assoc [
            ("is_valid", `Bool false);
            ("error_message", `String ("Invalid ILL sequent: " ^ msg))
        ]
    | _ ->
        `Assoc [
            ("is_valid", `Bool false);
            ("error_message", `String "Unknown parsing error")
        ]

(* Parse a single ILL formula string.
   @param formula_string - User input for single formula
   @return Yojson.Basic.t - JSON with validation result
*)
let safe_parse_formula formula_string =
    try
        let raw_sequent = Ll_parser.main Ll_lexer.token (Lexing.from_string formula_string) in
        match raw_sequent with
        | {hyp=[]; cons=[raw_formula]} ->
            let ill_formula = convert_raw_formula_to_ill raw_formula in
            validate_ill_formula ill_formula;
            `Assoc [
                ("is_valid", `Bool true);
                ("formula", ill_formula_to_json ill_formula)
            ]
        | _ ->
            `Assoc [
                ("is_valid", `Bool false);
                ("error_message", `String "Input must contain exactly one ILL formula")
            ]
    with
    | Invalid_ILL_Connective conn ->
        `Assoc [
            ("is_valid", `Bool false);
            ("error_message", `String ("Invalid ILL connective: " ^ conn))
        ]
    | _ ->
        `Assoc [
            ("is_valid", `Bool false);
            ("error_message", `String "Invalid ILL formula syntax")
        ]

(* Validate that a literal is acceptable in ILL.
   @param litt_string - Literal string to validate
   @return Yojson.Basic.t - JSON with validation result
*)
let safe_is_valid_litt litt_string =
    try
        let raw_sequent = Ll_parser.main Ll_lexer.token (Lexing.from_string litt_string) in
        match raw_sequent with
        | {hyp=[]; cons=[Raw_sequent.Litt s]} ->
            `Assoc [
                ("is_valid", `Bool true);
                ("value", `String s)
            ]
        | _ ->
            `Assoc [
                ("is_valid", `Bool false);
                ("error_message", `String "Input must contain exactly one literal")
            ]
    with
    | _ ->
        `Assoc [
            ("is_valid", `Bool false);
            ("error_message", `String "Invalid literal syntax")
        ]

(* HELPER FUNCTIONS *)

(* Generate user-friendly syntax examples for ILL.
   @return string - Syntax help text
*)
let get_ill_syntax_help () =
    "ILL Syntax:\n" ^
    "  Literals: A, B, C, ...\n" ^
    "  Tensor: A * B (multiplicative conjunction)\n" ^
    "  Plus: A + B (additive disjunction)\n" ^
    "  Lollipop: A -o B (linear implication)\n" ^
    "  One: 1 (multiplicative unit)\n" ^
    "  Top: T (additive unit)\n" ^
    "  Sequent: A, B |- C (context |- goal)"

(* Check if a string contains only valid ILL characters.
   @param s - String to check
   @return bool - True if valid ILL syntax characters
*)
let contains_only_ill_chars s =
    let valid_chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789*+1T|-() ,o-" in
    let rec check i =
        if i >= String.length s then true
        else if String.contains valid_chars s.[i] then check (i + 1)
        else false
    in
    check 0