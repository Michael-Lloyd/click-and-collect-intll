(* INTUITIONISTIC LINEAR LOGIC PROOF TREE REPRESENTATION
   
   This module defines proof trees for Intuitionistic Linear Logic (ILL).
   ILL differs from classical Linear Logic in several key ways:
   
   1. Asymmetric sequents: Γ ⊢ A (single conclusion)
   2. No exponentials: No !A or ?A connectives
   3. No multiplicative disjunction: No ⅋ connective  
   4. No additive conjunction: No & connective
   5. Has linear implication: A ⊸ B connective
   
   Each proof tree node represents an inference rule application with its premises.
*)

open Ill_sequent

(* ILL proof tree data structure.
   Each constructor corresponds to an ILL inference rule.
   
   Key differences from classical LL proofs:
   - No Par_proof, With_proof (removed connectives)
   - No exponential proofs (Promotion_proof, Dereliction_proof, etc.)
   - Added Lollipop_proof for linear implication
   - All sequents have single conclusions
*)
type ill_proof =
    | ILL_Axiom_proof of string                                           (* ax: A ⊢ A *)
    | ILL_One_proof                                                       (* 1: ⊢ 1 *)
    | ILL_Top_proof of formula list                                       (* ⊤: Γ ⊢ ⊤ *)
    | ILL_Tensor_proof of formula list * formula * formula * ill_proof * ill_proof  (* ⊗: Γ,Δ ⊢ A⊗B / Γ ⊢ A & Δ ⊢ B *)
    | ILL_Plus_left_proof of formula list * formula * formula * ill_proof          (* ⊕₁: Γ ⊢ A⊕B / Γ ⊢ A *)
    | ILL_Plus_right_proof of formula list * formula * formula * ill_proof         (* ⊕₂: Γ ⊢ A⊕B / Γ ⊢ B *)
    | ILL_Lollipop_proof of formula list * formula * formula * ill_proof           (* ⊸: Γ ⊢ A⊸B / Γ,A ⊢ B *)
    | ILL_Hypothesis_proof of ill_sequent;;                              (* open goal (leaf) *)

(* Exception for invalid proof operations *)
exception ILL_Proof_Exception of bool * string;;

(* PROOF TREE MANIPULATION FUNCTIONS *)

(* Extract the conclusion sequent from a proof tree.
   Every proof tree proves some sequent - this extracts it.
   @param proof - ILL proof tree
   @return ill_sequent - The sequent that this proof establishes
*)
let get_conclusion_sequent = function
    | ILL_Axiom_proof atom -> 
        { context = [Litt atom]; goal = Litt atom }
    | ILL_One_proof -> 
        { context = []; goal = One }
    | ILL_Top_proof context -> 
        { context = context; goal = Top }
    | ILL_Tensor_proof (context, f1, f2, _, _) -> 
        { context = context; goal = Tensor (f1, f2) }
    | ILL_Plus_left_proof (context, f1, f2, _) -> 
        { context = context; goal = Plus (f1, f2) }
    | ILL_Plus_right_proof (context, f1, f2, _) -> 
        { context = context; goal = Plus (f1, f2) }
    | ILL_Lollipop_proof (context, f1, f2, _) -> 
        { context = context; goal = Lollipop (f1, f2) }
    | ILL_Hypothesis_proof sequent -> 
        sequent

(* Get all immediate sub-proofs (premises) of a proof tree node.
   @param proof - ILL proof tree
   @return ill_proof list - List of premise proofs
*)
let get_premises = function
    | ILL_Axiom_proof _ -> []
    | ILL_One_proof -> []
    | ILL_Top_proof _ -> []
    | ILL_Tensor_proof (_, _, _, p1, p2) -> [p1; p2]
    | ILL_Plus_left_proof (_, _, _, p) -> [p]
    | ILL_Plus_right_proof (_, _, _, p) -> [p]
    | ILL_Lollipop_proof (_, _, _, p) -> [p]
    | ILL_Hypothesis_proof _ -> []

(* Replace the premises of a proof tree with new sub-proofs.
   Used for proof tree construction and manipulation.
   @param proof - Original proof tree
   @param new_premises - List of new sub-proofs
   @return ill_proof - Updated proof tree
*)
let set_premises proof new_premises = match proof, new_premises with
    | ILL_Axiom_proof _, [] -> proof
    | ILL_One_proof, [] -> proof
    | ILL_Top_proof _, [] -> proof
    | ILL_Tensor_proof (ctx, f1, f2, _, _), [p1; p2] -> ILL_Tensor_proof (ctx, f1, f2, p1, p2)
    | ILL_Plus_left_proof (ctx, f1, f2, _), [p] -> ILL_Plus_left_proof (ctx, f1, f2, p)
    | ILL_Plus_right_proof (ctx, f1, f2, _), [p] -> ILL_Plus_right_proof (ctx, f1, f2, p)
    | ILL_Lollipop_proof (ctx, f1, f2, _), [p] -> ILL_Lollipop_proof (ctx, f1, f2, p)
    | ILL_Hypothesis_proof _, [] -> proof
    | _ -> raise (ILL_Proof_Exception (false, "Invalid premise count for proof type"))

(* PROOF CONSTRUCTION FROM RULE REQUESTS *)

(* Apply an ILL inference rule to create a new proof tree.
   This is the main entry point called by the rule application system.
   @param sequent - The sequent to apply the rule to
   @param notations - User-defined formula notations
   @param rule_request - The specific rule to apply
   @return ill_proof - New proof tree with rule applied
*)
let from_sequent_and_rule_request sequent _notations _rule_request =
    (* TODO: Implement ILL rule application logic *)
    (* For now, just return a hypothesis proof as a stub *)
    let ill_seq = sequent_list_to_ill_sequent sequent in
    ILL_Hypothesis_proof ill_seq

(* PROOF VALIDATION *)

(* Check if a proof tree is complete (no open hypotheses).
   @param proof - ILL proof tree to check
   @return bool - True if proof is complete
*)
let rec is_complete_proof = function
    | ILL_Hypothesis_proof _ -> false  (* Open hypothesis *)
    | ILL_Axiom_proof _ -> true
    | ILL_One_proof -> true
    | ILL_Top_proof _ -> true
    | ILL_Tensor_proof (_, _, _, p1, p2) -> is_complete_proof p1 && is_complete_proof p2
    | ILL_Plus_left_proof (_, _, _, p) -> is_complete_proof p
    | ILL_Plus_right_proof (_, _, _, p) -> is_complete_proof p
    | ILL_Lollipop_proof (_, _, _, p) -> is_complete_proof p

(* Check if a proof tree is valid (rules correctly applied).
   @param proof - ILL proof tree to validate
   @return bool - True if proof is valid
*)
let rec is_valid_proof proof =
    (* TODO: Implement detailed proof validation *)
    (* For now, just check structural validity *)
    match proof with
    | ILL_Hypothesis_proof _ -> true  (* Hypotheses are always valid *)
    | ILL_Axiom_proof _ -> true       (* TODO: Check axiom validity *)
    | ILL_One_proof -> true
    | ILL_Top_proof _ -> true
    | ILL_Tensor_proof (_, _, _, p1, p2) -> is_valid_proof p1 && is_valid_proof p2
    | ILL_Plus_left_proof (_, _, _, p) -> is_valid_proof p
    | ILL_Plus_right_proof (_, _, _, p) -> is_valid_proof p
    | ILL_Lollipop_proof (_, _, _, p) -> is_valid_proof p

(* JSON SERIALIZATION *)

(* Convert ILL proof tree to JSON representation for frontend.
   @param proof - ILL proof tree
   @return Yojson.Basic.t - JSON representation
*)
let to_json proof =
    (* TODO: Implement JSON serialization for ILL proofs *)
    (* For now, return a basic structure *)
    match proof with
    | ILL_Hypothesis_proof _ill_seq ->
        `Assoc [
            ("s", `Assoc [("cons", `List [])]);  (* Stub sequent *)
            ("ar", `Null)  (* No applied rule *)
        ]
    | _ ->
        `Assoc [
            ("s", `Assoc [("cons", `List [])]);  (* Stub sequent *)
            ("ar", `Assoc [("rr", `Assoc [("r", `String "stub")]); ("p", `List [])])
        ]

(* Parse ILL proof tree from JSON representation.
   @param json - JSON representation from frontend
   @return ill_proof - Parsed ILL proof tree
*)
let from_json _json =
    (* TODO: Implement JSON deserialization for ILL proofs *)
    (* For now, return a simple hypothesis proof *)
    let stub_sequent = { context = []; goal = Litt "A" } in
    ILL_Hypothesis_proof stub_sequent

(* PROOF STATISTICS *)

(* Count the number of inference rules used in a proof.
   @param proof - ILL proof tree
   @return int - Number of inference rule applications
*)
let rec count_inference_rules = function
    | ILL_Hypothesis_proof _ -> 0
    | ILL_Axiom_proof _ -> 1
    | ILL_One_proof -> 1
    | ILL_Top_proof _ -> 1
    | ILL_Tensor_proof (_, _, _, p1, p2) -> 1 + count_inference_rules p1 + count_inference_rules p2
    | ILL_Plus_left_proof (_, _, _, p) -> 1 + count_inference_rules p
    | ILL_Plus_right_proof (_, _, _, p) -> 1 + count_inference_rules p
    | ILL_Lollipop_proof (_, _, _, p) -> 1 + count_inference_rules p

(* Count the number of open hypotheses in a proof.
   @param proof - ILL proof tree  
   @return int - Number of unproven goals
*)
let rec count_open_hypotheses = function
    | ILL_Hypothesis_proof _ -> 1
    | ILL_Axiom_proof _ -> 0
    | ILL_One_proof -> 0
    | ILL_Top_proof _ -> 0
    | ILL_Tensor_proof (_, _, _, p1, p2) -> count_open_hypotheses p1 + count_open_hypotheses p2
    | ILL_Plus_left_proof (_, _, _, p) -> count_open_hypotheses p
    | ILL_Plus_right_proof (_, _, _, p) -> count_open_hypotheses p
    | ILL_Lollipop_proof (_, _, _, p) -> count_open_hypotheses p