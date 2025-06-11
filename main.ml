open Opium
open Lwt.Syntax

(* WEB SERVER ENTRY POINT FOR CLICK-AND-COLLECT LINEAR LOGIC PROVER
   
   This is the main OCaml backend server that provides REST API endpoints
   for parsing Linear Logic sequents, applying proof rules, and exporting proofs.
   Uses the Opium web framework built on top of Lwt for async I/O.
*)

(* UTILITY FUNCTIONS *)

(* Convert string to boolean - accepts "true", "1" as true, everything else as false *)
let bool_from_string s =
    s = "true" || s = "1"

(* Extract and decompress JSON from HTTP request body.
   The frontend sends compressed JSON to reduce bandwidth,
   so we need to uncompress it before parsing.
*)
let from_req req =
    let+ json = Request.to_json_exn req in
    Yojson.Basic.from_string (Proof_compression.uncompress_json (Yojson.Safe.to_string json))

(* Generic handler for GET requests with URL parameters.
   Takes a handler function that processes the parameter and returns JSON,
   handles errors by logging them and re-raising.
*)
let common_get_handler handler_function handler_param req =
    Lwt.catch (fun () ->
        Lwt.return (Response.of_json (handler_function (Router.param req handler_param))))
    (fun t -> Logs.err (fun m -> m "%s" (Printexc.to_string t));
        Request.pp_hum Format.std_formatter req; raise t)

(* Generic handler for POST requests with JSON bodies.
   Handles decompression, error cases, and response formatting.
   Handler functions return (bool * response) where bool indicates success.
*)
let common_post_handler ok_response_method bad_request_response_method transform_message handler_function req =
    Lwt.catch (fun () ->
        try
            let+ request_as_json = from_req req in
            let technical_success, response = handler_function request_as_json in
            if technical_success then ok_response_method response
            else bad_request_response_method response
        with Yojson.Json_error _ -> Lwt.return (bad_request_response_method (transform_message "Body content is not a valid json")))
    (fun t -> Logs.err (fun m -> m "%s" (Printexc.to_string t));
        Request.pp_hum Format.std_formatter req; raise t)

(* Handler for endpoints that return JSON responses *)
let json_handler json_function req =
    common_post_handler (Response.of_json ~status:`OK) (Response.of_json ~status:`Bad_request) (fun s -> `String s) json_function req

(* Handler for endpoints that return plain text responses (like LaTeX, Coq code) *)
let plain_text_handler plain_text_function req =
    common_post_handler (Response.of_plain_text ~status:`OK) (Response.of_plain_text ~status:`Bad_request) (fun s -> s) plain_text_function req

(* HTTP REQUEST HANDLERS - API ENDPOINTS *)

(* Serve static files (CSS, JS, images) from ./static directory *)
let static_handler = Middleware.static_unix ~local_path:"./static" ~uri_prefix:"/static" ();;

(* Serve the main HTML page at root URL *)
let index_handler _request =
    Response.of_file "./index.html" ~mime:"text/html; charset=utf-8";;

(* Parse a sequent from URL parameter and return proof structure
   GET /parse_sequent/:sequent_as_string
   Example: /parse_sequent/A,A^ will parse "A,A^" as a sequent
*)
let parse_sequent_handler req =
    common_get_handler Parse_sequent.safe_parse "sequent_as_string" req ;;

(* Parse empty sequent (for initialization)
   GET /parse_sequent/
*)
let parse_empty_sequent_handler _req =
    Lwt.return (Response.of_json (Parse_sequent.safe_parse ""));;

(* Parse a single formula from URL parameter  
   GET /parse_formula/:formula_as_string
   Example: /parse_formula/A*B will parse "A*B" as a tensor formula
*)
let parse_formula_handler req =
    common_get_handler Parse_sequent.safe_parse_formula "formula_as_string" req;;

(* Validate that a string is a valid literal (atomic proposition)
   GET /is_valid_litt/:litt
*)
let is_valid_litt_handler req =
    common_get_handler Parse_sequent.safe_is_valid_litt "litt" req;;

(* Check if a sequent is provable using automated proving
   POST /is_sequent_provable
   Body: JSON with sequent data
*)
let is_sequent_provable_handler req =
    json_handler Is_sequent_provable.is_sequent_provable req

(* Apply a single inference rule to a sequent
   POST /apply_rule  
   Body: JSON with rule application request
*)
let apply_rule_handler req =
    json_handler Apply_rule.apply_rule req

(* Apply reversible rules automatically to simplify sequent
   POST /auto_reverse_sequent
   Body: JSON with sequent data
*)
let auto_reverse_handler req =
    json_handler Auto_reverse_sequent.auto_reverse_sequent req

(* Attempt to automatically prove a sequent
   POST /auto_prove_sequent
   Body: JSON with sequent data
*)
let auto_prove_handler req =
    json_handler Auto_prove_sequent.auto_prove_sequent req

(* Compress a proof for efficient storage/transmission
   POST /compress_proof
   Body: JSON with proof data
*)
let compress_proof_handler req =
    json_handler Proof_compression.compress_proof req

(* Decompress a previously compressed proof
   POST /uncompress_proof  
   Body: JSON with compressed proof data
*)
let uncompress_proof_handler req =
    json_handler Proof_compression.uncompress_proof req;;

(* Export proof as Coq code for verification in Coq theorem prover
   POST /export_as_coq
   Body: JSON with proof data
*)
let export_as_coq_handler req =
    plain_text_handler Export_as_coq.export_as_coq req

(* Export proof as LaTeX/PDF/PNG for visual presentation
   POST /export_as_latex/:format/:implicit_exchange
   Formats: tex, pdf, png, ascii, utf8
   implicit_exchange: true/false for whether to show exchange rules
*)
let export_as_latex_handler req =
    let implicit_exchange = bool_from_string (Router.param req "implicit_exchange") in
    let format = Router.param req "format" in
    let+ response = plain_text_handler (Export_as_latex.export_as_latex implicit_exchange format) req in
    if format = "png" then Response.set_content_type "image/png" response
    else if format = "pdf" then Response.set_content_type "application/pdf" response
    else response

(* Get available proof transformation options for a given proof
   POST /get_proof_transformation_options
   Body: JSON with proof data
*)
let get_proof_transformation_options_handler req =
    json_handler Proof_transformation.get_proof_transformation_options req

(* Apply a proof transformation (e.g., cut elimination, commuting rules)
   POST /apply_transformation
   Body: JSON with transformation request
*)
let apply_transformation_handler req =
    json_handler Proof_transformation.apply_transformation req

(** Configure the logger *)
let set_logger () =
  Logs.set_reporter (Logs_fmt.reporter ());
  Logs.set_level (Some Logs.Debug)

let _ =
  set_logger ();
  App.empty
  |> App.middleware static_handler
  |> App.get "/" index_handler
  |> App.get "/parse_sequent/:sequent_as_string" parse_sequent_handler
  |> App.get "/parse_sequent/" parse_empty_sequent_handler
  |> App.get "/parse_formula/:formula_as_string" parse_formula_handler
  |> App.get "/is_valid_litt/:litt" is_valid_litt_handler
  |> App.post "/is_sequent_provable" is_sequent_provable_handler
  |> App.post "/apply_rule" apply_rule_handler
  |> App.post "/auto_reverse_sequent" auto_reverse_handler
  |> App.post "/auto_prove_sequent" auto_prove_handler
  |> App.post "/compress_proof" compress_proof_handler
  |> App.post "/uncompress_proof" uncompress_proof_handler
  |> App.post "/export_as_coq" export_as_coq_handler
  |> App.post "/export_as_latex/:format/:implicit_exchange" export_as_latex_handler
  |> App.post "/get_proof_transformation_options" get_proof_transformation_options_handler
  |> App.post "/apply_transformation" apply_transformation_handler
  |> App.run_command
;;