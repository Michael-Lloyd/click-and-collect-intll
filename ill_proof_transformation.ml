open Ill_sequent
open Ill_proof
open Ill_transform_request

(* Exception for transformation errors *)
exception ILL_Transform_exception of string

(* Exception for pedagogical warnings *)
exception ILL_Pedagogic_exception of string

(* TRANSFORMATION CAPABILITY CHECKING *)

(* Check if we can commute a cut with the left premise in ILL.
   ILL cut commutation is simpler than classical LL since we have asymmetric sequents.
   @param cut_formula_position - Position of cut formula in context  
   @param proof - Left premise proof
   @return (bool * string) - (can_commute, reason) *)
let can_commute_with_cut_left _cut_formula_position cut_formula = function
    | ILL_Axiom_proof atom when cut_formula = Litt atom -> 
        Printf.eprintf "[ILL-TRANSFORM] can_commute_with_cut_left: Axiom %s matches cut formula Litt %s - VALID\n%!" atom atom;
        true, "Eliminate ax-cut"
    | ILL_Axiom_proof atom -> 
        Printf.eprintf "[ILL-TRANSFORM] can_commute_with_cut_left: Axiom %s doesn't match cut formula - INVALID\n%!" atom;
        false, "Axiom doesn't match cut formula"
    | ILL_Hypothesis_proof sequent when sequent.goal = cut_formula ->
        (* Check if this is actually an axiom case: goal appears in context *)
        if List.mem cut_formula sequent.context then (
            Printf.eprintf "[ILL-TRANSFORM] can_commute_with_cut_left: Hypothesis is actually an axiom case - VALID\n%!";
            true, "Eliminate ax-cut (from hypothesis)"
        ) else (
            Printf.eprintf "[ILL-TRANSFORM] can_commute_with_cut_left: Hypothesis goal matches cut formula but it's incomplete!\n%!";
            Printf.eprintf "[ILL-TRANSFORM] ERROR: Goal not in context, this is an open goal\n%!";
            false, "Cannot eliminate cut: left side is an incomplete hypothesis"
        )
    | ILL_Hypothesis_proof sequent ->
        Printf.eprintf "[ILL-TRANSFORM] can_commute_with_cut_left: Hypothesis goal doesn't match cut formula - INVALID\n%!";
        Printf.eprintf "[ILL-TRANSFORM] Hypothesis context: %d formulas, goal: (formula), cut formula: (formula)\n%!" (List.length sequent.context);
        false, "Hypothesis doesn't prove cut formula"
    | ILL_One_right_proof when cut_formula = One -> 
        Printf.eprintf "[ILL-TRANSFORM] can_commute_with_cut_left: One right proof matches cut formula One - VALID\n%!";
        true, "Eliminate 1-cut"
    | ILL_One_right_proof -> 
        Printf.eprintf "[ILL-TRANSFORM] can_commute_with_cut_left: One right proof doesn't match cut formula - INVALID\n%!";
        false, "One right rule doesn't match cut formula"
    | ILL_One_left_proof (_, _) ->
        (* One left can be commuted with cut *)
        true, "Commute with 1L rule"
    | ILL_Top_proof _ when cut_formula = Top -> 
        Printf.eprintf "[ILL-TRANSFORM] can_commute_with_cut_left: Top proof matches cut formula Top - VALID\n%!";
        true, "Commute with ⊤ rule"
    | ILL_Top_proof _ -> 
        Printf.eprintf "[ILL-TRANSFORM] can_commute_with_cut_left: Top proof doesn't match cut formula - INVALID\n%!";
        false, "Top rule doesn't match cut formula"
    | ILL_Tensor_proof (_, f1, f2, left_premise, right_premise) when cut_formula = Tensor (f1, f2) -> 
        let _ = (left_premise, right_premise) in  (* TODO: Use for advanced commutation *)
        true, "Commute with ⊗ rule"
    | ILL_Tensor_proof (_, _, _, _, _) -> 
        false, "Tensor ⊗ doesn't match cut formula"
    | ILL_Tensor_left_proof (_, formula1, formula2, premise) -> 
        let _ = (formula1, formula2, premise) in  (* TODO: Validate commutation logic *)
        true, "Commute with ⊗L rule"
    | ILL_With_left_1_proof (_, with_formula, premise) -> 
        let _ = (with_formula, premise) in  (* TODO: Validate commutation logic *)
        true, "Commute with &L₁ rule"
    | ILL_With_left_2_proof (_, with_formula, premise) -> 
        let _ = (with_formula, premise) in  (* TODO: Validate commutation logic *)
        true, "Commute with &L₂ rule"
    | ILL_With_right_proof (_, f1, f2, left_premise, right_premise) when cut_formula = With (f1, f2) -> 
        let _ = (left_premise, right_premise) in  (* TODO: Use for advanced commutation *)
        true, "Commute with &R rule"
    | ILL_With_right_proof (_, _, _, _, _) -> 
        false, "With & doesn't match cut formula"
    | ILL_Plus_left_proof (_, formula1, formula2, left_premise, right_premise) -> 
        let _ = (formula1, formula2, left_premise, right_premise) in  (* TODO: Validate commutation logic *)
        true, "Commute with ⊕L rule"
    | ILL_Plus_right_1_proof (_, f1, f2, premise) when cut_formula = Plus (f1, f2) -> 
        let _ = premise in  (* TODO: Use for advanced commutation *)
        true, "Commute with ⊕₁ rule"
    | ILL_Plus_right_1_proof (_, _, _, _) -> 
        false, "Plus ⊕₁ doesn't match cut formula"
    | ILL_Plus_right_2_proof (_, f1, f2, premise) when cut_formula = Plus (f1, f2) -> 
        let _ = premise in  (* TODO: Use for advanced commutation *)
        true, "Commute with ⊕₂ rule"
    | ILL_Plus_right_2_proof (_, _, _, _) -> 
        false, "Plus ⊕₂ doesn't match cut formula"
    | ILL_Lollipop_proof (_, f1, f2, premise) when cut_formula = Lollipop (f1, f2) -> 
        let _ = premise in  (* TODO: Use for advanced commutation *)
        true, "Commute with ⊸ rule"
    | ILL_Lollipop_proof (_, _, _, _) -> 
        false, "Lollipop ⊸ doesn't match cut formula"
    | ILL_Lollipop_left_proof (_, antecedent, consequent, left_premise, right_premise) -> 
        let _ = (antecedent, consequent, left_premise, right_premise) in  (* TODO: Validate commutation logic *)
        true, "Commute with ⊸L rule"
    | ILL_Cut_proof (head_context, cut_f, tail_context, left_premise, right_premise) -> 
        let _ = (head_context, cut_f, tail_context, left_premise, right_premise) in  (* TODO: Use for advanced cut commutation *)
        true, "Commute with cut rule"
    | ILL_Weakening_proof (_, _, _, _) -> 
        (* TODO: Implement proper cut commutation with weakening rule *)
        true, "Commute with weakening rule"
    | ILL_Contraction_proof (_, _, _, _) -> 
        (* TODO: Implement proper cut commutation with contraction rule *)
        true, "Commute with contraction rule"
    | ILL_Dereliction_proof (_, _, _, _) -> 
        (* TODO: Implement proper cut commutation with dereliction rule *)
        true, "Commute with dereliction rule"
    | ILL_Promotion_proof (_, _, _) -> 
        (* TODO: Implement proper cut commutation with promotion rule *)
        true, "Commute with promotion rule"

(* Check if we can commute a cut with the right premise in ILL.
   @param cut_context - Context where cut formula is inserted
   @param proof - Right premise proof
   @return (bool * string) - (can_commute, reason) *)
let can_commute_with_cut_right cut_context = function
    | ILL_Axiom_proof atom -> 
        (match cut_context with 
         | [Litt atom_cut] when atom = atom_cut -> true, "Eliminate ax-cut"
         | _ -> false, "Axiom doesn't match cut context")
    | ILL_Hypothesis_proof sequent -> 
        (* Check if this is actually an axiom case: cut formula appears in context and goal *)
        (match cut_context with
         | [cut_formula] when sequent.goal = cut_formula && List.mem cut_formula sequent.context ->
             Printf.eprintf "[ILL-TRANSFORM] can_commute_with_cut_right: Hypothesis is actually an axiom case - VALID\n%!";
             true, "Eliminate ax-cut (from hypothesis)"
         | _ ->
             Printf.eprintf "[ILL-TRANSFORM] can_commute_with_cut_right: Hypothesis proof is incomplete\n%!";
             false, "Cannot eliminate cut: right side is an incomplete hypothesis")
    | ILL_One_right_proof -> 
        (match cut_context with 
         | [One] -> true, "Eliminate 1-cut"
         | _ -> false, "One right rule doesn't match cut context")
    | ILL_One_left_proof (context, _) when 
        (match cut_context with [] -> true | cut_formula :: _ -> not (List.mem cut_formula context)) -> 
        true, "Commute with 1L rule"
    | ILL_One_left_proof (_, _) ->
        false, "Cannot commute with 1L rule due to context conflict"
    | ILL_Top_proof _ -> 
        (match cut_context with 
         | [Top] -> true, "Commute with ⊤ rule"
         | _ -> false, "Top rule doesn't match cut context")
    | ILL_Tensor_left_proof (context, _, _, _) when 
        (match cut_context with [] -> true | cut_formula :: _ -> not (List.mem cut_formula context)) -> 
        true, "Commute with ⊗L rule"
    | ILL_With_left_1_proof (context, _, _) when 
        (match cut_context with [] -> true | cut_formula :: _ -> not (List.mem cut_formula context)) -> 
        true, "Commute with &L₁ rule"
    | ILL_With_left_2_proof (context, _, _) when 
        (match cut_context with [] -> true | cut_formula :: _ -> not (List.mem cut_formula context)) -> 
        true, "Commute with &L₂ rule"
    | ILL_Plus_left_proof (context, _, _, _, _) when 
        (match cut_context with [] -> true | cut_formula :: _ -> not (List.mem cut_formula context)) -> 
        true, "Commute with ⊕L rule"
    | ILL_Lollipop_left_proof (context, _, _, _, _) when 
        (match cut_context with [] -> true | cut_formula :: _ -> not (List.mem cut_formula context)) -> 
        true, "Commute with ⊸L rule"
    | ILL_Cut_proof (_, _, _, _, _) -> 
        true, "Commute with cut rule"
    | ILL_Tensor_left_proof (_, _, _, _) -> 
        false, "Cannot commute with ⊗L rule due to context conflict"
    | ILL_With_left_1_proof (_, _, _) -> 
        false, "Cannot commute with &L₁ rule due to context conflict"
    | ILL_With_left_2_proof (_, _, _) -> 
        false, "Cannot commute with &L₂ rule due to context conflict"
    | ILL_Plus_left_proof (_, _, _, _, _) -> 
        false, "Cannot commute with ⊕L rule due to context conflict"
    | ILL_Lollipop_left_proof (_, _, _, _, _) -> 
        false, "Cannot commute with ⊸L rule due to context conflict"
    | ILL_Tensor_proof (_, _, _, _, _) -> 
        false, "Cannot commute with ⊗R rule on right side"
    | ILL_With_right_proof (_, _, _, _, _) -> 
        false, "Cannot commute with &R rule on right side"
    | ILL_Plus_right_1_proof (_, _, _, _) -> 
        false, "Cannot commute with ⊕₁ rule on right side"
    | ILL_Plus_right_2_proof (_, _, _, _) -> 
        false, "Cannot commute with ⊕₂ rule on right side"
    | ILL_Lollipop_proof (_, _, _, _) -> 
        false, "Cannot commute with ⊸R rule on right side"
    | ILL_Weakening_proof (_, _, _, _) -> 
        (* TODO: Implement proper cut commutation with weakening rule on right side *)
        false, "Cannot commute with weakening rule on right side"
    | ILL_Contraction_proof (_, _, _, _) -> 
        (* TODO: Implement proper cut commutation with contraction rule on right side *)
        false, "Cannot commute with contraction rule on right side"
    | ILL_Dereliction_proof (_, _, _, _) -> 
        (* TODO: Implement proper cut commutation with dereliction rule on right side *)
        false, "Cannot commute with dereliction rule on right side"
    | ILL_Promotion_proof (_, _, _) -> 
        (* TODO: Implement proper cut commutation with promotion rule on right side *)
        false, "Cannot commute with promotion rule on right side"

(* Check if we can eliminate a key case in ILL cut elimination.
   Key cases occur when the cut formula is the principal formula of both premises.
   @param left_proof - Left premise of cut
   @param right_proof - Right premise of cut
   @return (bool * string) - (can_eliminate, reason) *)
let can_cut_key_case left_proof right_proof = match left_proof, right_proof with
    (* Tensor/Tensor-left key case: A⊗B cut *)
    | ILL_Tensor_proof (_, f1, f2, _, _), ILL_Tensor_left_proof (_, g1, g2, _) 
        when f1 = g1 && f2 = g2 -> 
        true, "Eliminate ⊗/⊗L key-case"
    
    (* With/With-left key cases: A&B cut *)
    | ILL_With_right_proof (_, f1, f2, _, _), ILL_With_left_1_proof (_, g, _) 
        when With (f1, f2) = g -> 
        true, "Eliminate &R/&L₁ key-case"
    | ILL_With_right_proof (_, f1, f2, _, _), ILL_With_left_2_proof (_, g, _) 
        when With (f1, f2) = g -> 
        true, "Eliminate &R/&L₂ key-case"
    
    (* Plus/Plus-left key cases: A⊕B cut *)
    | ILL_Plus_right_1_proof (_, f1, f2, _), ILL_Plus_left_proof (_, g1, g2, _, _) 
        when f1 = g1 && f2 = g2 -> 
        true, "Eliminate ⊕₁/⊕L key-case"
    | ILL_Plus_right_2_proof (_, f1, f2, _), ILL_Plus_left_proof (_, g1, g2, _, _) 
        when f1 = g1 && f2 = g2 -> 
        true, "Eliminate ⊕₂/⊕L key-case"
    
    (* Lollipop/Lollipop-left key case: A⊸B cut *)
    | ILL_Lollipop_proof (_, f1, f2, _), ILL_Lollipop_left_proof (_, g1, g2, _, _) 
        when f1 = g1 && f2 = g2 -> 
        true, "Eliminate ⊸/⊸L key-case"
    
    (* Axiom key-case: when cut formula matches axiom on both sides *)
    | ILL_Axiom_proof atom1, ILL_Axiom_proof atom2 when atom1 = atom2 ->
        true, "Eliminate axiom-axiom key-case"
    
    (* Hypothesis key-case: when both sides are hypothesis proofs *)
    | ILL_Hypothesis_proof left_seq, ILL_Hypothesis_proof right_seq ->
        Printf.eprintf "[ILL-TRANSFORM] can_cut_key_case: Found hypothesis-hypothesis case\n%!";
        Printf.eprintf "[ILL-TRANSFORM] Left sequent: %d context formulas, goal: (formula)\n%!" (List.length left_seq.context);
        Printf.eprintf "[ILL-TRANSFORM] Right sequent: %d context formulas, goal: (formula)\n%!" (List.length right_seq.context);
        
        (* Check if either side is actually an axiom case *)
        let left_is_axiom = List.mem left_seq.goal left_seq.context in
        let right_is_axiom = List.mem right_seq.goal right_seq.context in
        
        if left_is_axiom || right_is_axiom then (
            Printf.eprintf "[ILL-TRANSFORM] At least one side is an axiom case - VALID\n%!";
            true, "Eliminate hypothesis-axiom key-case"
        ) else (
            Printf.eprintf "[ILL-TRANSFORM] ERROR: Both sides are open hypotheses - no actual proof exists!\n%!";
            Printf.eprintf "[ILL-TRANSFORM] Cut elimination requires at least one side to be a complete proof\n%!";
            false, "Cannot eliminate cut: both sides are incomplete hypotheses"
        )
    
    | _ -> false, "No key-case available"

(* Get available transformation options for an ILL proof node.
   @param proof - ILL proof to analyze
   @return (ill_transform_request * (bool * string)) list - Available transformations with descriptions *)
let get_transform_options = function
    | ILL_Axiom_proof _ -> 
        [ILL_Expand_axiom, (true, "One step axiom expansion");
         ILL_Expand_axiom_full, (true, "Full axiom expansion")]
    
    | ILL_Cut_proof (head_ctx, cut_formula, tail_ctx, left_proof, right_proof) ->
        Printf.eprintf "[ILL-TRANSFORM] get_transform_options: Analyzing cut proof\n%!";
        Printf.eprintf "[ILL-TRANSFORM] Head context: %d formulas, tail context: %d formulas\n%!" (List.length head_ctx) (List.length tail_ctx);
        Printf.eprintf "[ILL-TRANSFORM] Cut formula: (formula type), Left proof type: %s, Right proof type: %s\n%!" 
            (match left_proof with | ILL_Axiom_proof _ -> "Axiom" | ILL_Hypothesis_proof _ -> "Hypothesis" | ILL_One_right_proof -> "OneRight" | ILL_One_left_proof _ -> "OneLeft" | ILL_Top_proof _ -> "Top" | ILL_Tensor_proof _ -> "Tensor" | ILL_Tensor_left_proof _ -> "TensorLeft" | ILL_With_left_1_proof _ -> "WithLeft1" | ILL_With_left_2_proof _ -> "WithLeft2" | ILL_With_right_proof _ -> "WithRight" | ILL_Plus_left_proof _ -> "PlusLeft" | ILL_Plus_right_1_proof _ -> "PlusRight1" | ILL_Plus_right_2_proof _ -> "PlusRight2" | ILL_Lollipop_proof _ -> "Lollipop" | ILL_Lollipop_left_proof _ -> "LollipopLeft" | ILL_Cut_proof _ -> "Cut" | ILL_Weakening_proof _ -> "Weakening" | ILL_Contraction_proof _ -> "Contraction" | ILL_Dereliction_proof _ -> "Dereliction" | ILL_Promotion_proof _ -> "Promotion")
            (match right_proof with | ILL_Axiom_proof _ -> "Axiom" | ILL_Hypothesis_proof _ -> "Hypothesis" | ILL_One_right_proof -> "OneRight" | ILL_One_left_proof _ -> "OneLeft" | ILL_Top_proof _ -> "Top" | ILL_Tensor_proof _ -> "Tensor" | ILL_Tensor_left_proof _ -> "TensorLeft" | ILL_With_left_1_proof _ -> "WithLeft1" | ILL_With_left_2_proof _ -> "WithLeft2" | ILL_With_right_proof _ -> "WithRight" | ILL_Plus_left_proof _ -> "PlusLeft" | ILL_Plus_right_1_proof _ -> "PlusRight1" | ILL_Plus_right_2_proof _ -> "PlusRight2" | ILL_Lollipop_proof _ -> "Lollipop" | ILL_Lollipop_left_proof _ -> "LollipopLeft" | ILL_Cut_proof _ -> "Cut" | ILL_Weakening_proof _ -> "Weakening" | ILL_Contraction_proof _ -> "Contraction" | ILL_Dereliction_proof _ -> "Dereliction" | ILL_Promotion_proof _ -> "Promotion");
        
        let cut_position = List.length head_ctx in
        let _ = tail_ctx in  (* TODO: Use tail_ctx for more sophisticated transformation options *)
        
        Printf.eprintf "[ILL-TRANSFORM] Checking left commutation at position %d...\n%!" cut_position;
        let commute_left, commute_left_msg = can_commute_with_cut_left cut_position cut_formula left_proof in
        Printf.eprintf "[ILL-TRANSFORM] Left commutation result: %b (%s)\n%!" commute_left commute_left_msg;
        
        Printf.eprintf "[ILL-TRANSFORM] Checking right commutation...\n%!";
        let commute_right, commute_right_msg = can_commute_with_cut_right [cut_formula] right_proof in
        Printf.eprintf "[ILL-TRANSFORM] Right commutation result: %b (%s)\n%!" commute_right commute_right_msg;
        
        Printf.eprintf "[ILL-TRANSFORM] Checking key-case elimination...\n%!";
        let key_case, key_case_msg = can_cut_key_case left_proof right_proof in
        Printf.eprintf "[ILL-TRANSFORM] Key-case result: %b (%s)\n%!" key_case key_case_msg;
        
        let cut_full = commute_left || commute_right || key_case in
        Printf.eprintf "[ILL-TRANSFORM] Full cut elimination possible: %b\n%!" cut_full;
        
        let options = [ILL_Eliminate_cut_left, (commute_left, commute_left_msg ^ " on the left");
         ILL_Eliminate_cut_key_case, (key_case, key_case_msg);
         ILL_Eliminate_cut_right, (commute_right, commute_right_msg ^ " on the right");
         ILL_Eliminate_cut_full, (cut_full, "Fully eliminate this cut")] in
        Printf.eprintf "[ILL-TRANSFORM] Returning %d transformation options\n%!" (List.length options);
        options
    
    | _ -> 
        []

(* Convert transformation options to JSON format for frontend.
   @param proof - ILL proof to analyze
   @return (string * Yojson.Basic.t) list - JSON representation *)
let get_transform_options_as_json proof =
    let transform_options = get_transform_options proof in
    ["transformOptions", `List (List.map (fun (transform_option, (enabled, title)) -> `Assoc [
        ("transformation", `String (Ill_transform_request.to_string transform_option));
        ("enabled", `Bool enabled);
        ("title", `String title)
        ]) transform_options)]

(* AXIOM EXPANSION *)

(* Expand an ILL axiom formula to its dual construction.
   ILL axiom expansion is simpler than classical LL since we have no par (⅋) connective.
   @param formula - Formula to expand  
   @return ill_proof - Expanded proof tree *)
let expand_axiom = function
    | One -> 
        (* 1 axiom becomes ⊢ 1 rule *)
        ILL_One_right_proof
    
    | Top -> 
        (* ⊤ axiom becomes Γ ⊢ ⊤ rule with any context *)
        ILL_Top_proof [Top]
    
    | Litt s -> 
        (* Literal axiom stays as axiom *)
        ILL_Axiom_proof s
    
    | Tensor (f1, f2) ->
        (* A⊗B axiom becomes: 
           A⊗B ⊢ A⊗B
           ============ ⊗L
           A, B ⊢ A⊗B
           ============ ⊗R  
           A ⊢ A, B ⊢ B *)
        let axiom1 = ILL_Axiom_proof (match f1 with Litt s -> s | _ -> "A") in
        let axiom2 = ILL_Axiom_proof (match f2 with Litt s -> s | _ -> "B") in
        let tensor_proof = ILL_Tensor_proof ([f1], f1, f2, axiom1, axiom2) in
        ILL_Tensor_left_proof ([Tensor (f1, f2)], f1, f2, tensor_proof)
    
    | With (f1, f2) ->
        (* A&B axiom becomes:
           A&B ⊢ A&B
           ========== &L₁  ========== &L₂
           A ⊢ A&B     B ⊢ A&B
           ==================== &R
           A&B ⊢ A&B *)
        let axiom1 = ILL_Axiom_proof (match f1 with Litt s -> s | _ -> "A") in
        let axiom2 = ILL_Axiom_proof (match f2 with Litt s -> s | _ -> "B") in
        let with_proof = ILL_With_right_proof ([With (f1, f2)], f1, f2, axiom1, axiom2) in
        with_proof
    
    | Plus (f1, f2) ->
        (* A⊕B axiom becomes:
           A⊕B ⊢ A⊕B
           ========== ⊕L
           A ⊢ A⊕B ∧ B ⊢ A⊕B
           A ⊢ A     B ⊢ B
           ===== ⊕₁  ===== ⊕₂ *)
        let axiom1 = ILL_Axiom_proof (match f1 with Litt s -> s | _ -> "A") in
        let axiom2 = ILL_Axiom_proof (match f2 with Litt s -> s | _ -> "B") in
        let plus1_proof = ILL_Plus_right_1_proof ([f1], f1, f2, axiom1) in
        let plus2_proof = ILL_Plus_right_2_proof ([f2], f1, f2, axiom2) in
        ILL_Plus_left_proof ([Plus (f1, f2)], f1, f2, plus1_proof, plus2_proof)
    
    | Lollipop (f1, f2) ->
        (* A⊸B axiom becomes:
           A⊸B ⊢ A⊸B
           ========== ⊸L
           A ⊢ A ∧ B ⊢ A⊸B
           =========== ⊸R  
           A, B ⊢ B *)
        let axiom1 = ILL_Axiom_proof (match f1 with Litt s -> s | _ -> "A") in
        let axiom2 = ILL_Axiom_proof (match f2 with Litt s -> s | _ -> "B") in
        let lollipop_proof = ILL_Lollipop_proof ([f1], f1, f2, axiom2) in
        ILL_Lollipop_left_proof ([Lollipop (f1, f2)], f1, f2, axiom1, lollipop_proof)
    
    | Ofcourse f ->
        (* TODO: Implement proper expansion for exponential formulas *)
        (* For now, create a simple axiom for the inner formula *)
        (match f with
         | Litt s -> ILL_Axiom_proof s
         | _ -> ILL_Axiom_proof "A")

(* Apply axiom expansion to a proof tree recursively.
   @param proof - Proof tree to expand
   @return ill_proof - Expanded proof tree *)
let expand_axiom_on_proof = function
    | ILL_Axiom_proof atom -> 
        expand_axiom (Litt atom)
    | _ -> 
        raise (ILL_Transform_exception "Can only expand axiom on axiom proofs")

(* Apply full axiom expansion recursively throughout a proof tree.
   @param proof - Proof tree to expand
   @return ill_proof - Fully expanded proof tree *)
let rec expand_axiom_full proof =
    let new_proof =
        try expand_axiom_on_proof proof
        with ILL_Transform_exception _ -> proof 
    in
    set_premises new_proof (List.map expand_axiom_full (get_premises new_proof))

(* CUT ELIMINATION *)

(* Apply cut elimination on the left premise of a cut.
   This commutes the cut with the left premise rule.
   @param cut_proof - Cut proof to transform
   @return ill_proof - Transformed proof *)
let eliminate_cut_left = function
    | ILL_Cut_proof (head_ctx, cut_formula, tail_ctx, left_proof, right_proof) ->
        (match left_proof with
         | ILL_Hypothesis_proof left_sequent when left_sequent.goal = cut_formula ->
             (* Hypothesis-cut elimination: left proves cut formula, return right proof *)
             right_proof
         
         | ILL_Axiom_proof atom when cut_formula = Litt atom ->
             (* Axiom-cut elimination: just return the right proof with context *)
             right_proof
         
         | ILL_One_right_proof when cut_formula = One ->
             (* One-cut elimination: right proof must have empty context where cut formula was *)
             right_proof
         
         | ILL_Tensor_proof (tensor_context, f1, f2, p1, p2) when cut_formula = Tensor (f1, f2) ->
             let _ = tensor_context in  (* TODO: Use context for more precise cut elimination *)
             (* Tensor-cut commutation: move cut above tensor rule *)
             let cut1 = ILL_Cut_proof (head_ctx, f1, tail_ctx, p1, right_proof) in
             let cut2 = ILL_Cut_proof (head_ctx, f2, tail_ctx, p2, right_proof) in
             ILL_Tensor_proof (head_ctx @ tail_ctx, f1, f2, cut1, cut2)
         
         | ILL_With_right_proof (with_context, f1, f2, p1, p2) when cut_formula = With (f1, f2) ->
             let _ = with_context in  (* TODO: Use context for more precise cut elimination *)
             (* With-cut commutation: move cut above with rule *)
             let cut1 = ILL_Cut_proof (head_ctx, cut_formula, tail_ctx, p1, right_proof) in
             let cut2 = ILL_Cut_proof (head_ctx, cut_formula, tail_ctx, p2, right_proof) in
             ILL_With_right_proof (head_ctx @ tail_ctx, f1, f2, cut1, cut2)
         
         | ILL_Plus_right_1_proof (plus_context, f1, f2, p1) when cut_formula = Plus (f1, f2) ->
             let _ = plus_context in  (* TODO: Use context for more precise cut elimination *)
             (* Plus-right-1-cut commutation: move cut above plus rule *)
             let cut1 = ILL_Cut_proof (head_ctx, cut_formula, tail_ctx, p1, right_proof) in
             ILL_Plus_right_1_proof (head_ctx @ tail_ctx, f1, f2, cut1)
         
         | ILL_Plus_right_2_proof (plus_context, f1, f2, p2) when cut_formula = Plus (f1, f2) ->
             let _ = plus_context in  (* TODO: Use context for more precise cut elimination *)
             (* Plus-right-2-cut commutation: move cut above plus rule *)
             let cut2 = ILL_Cut_proof (head_ctx, cut_formula, tail_ctx, p2, right_proof) in
             ILL_Plus_right_2_proof (head_ctx @ tail_ctx, f1, f2, cut2)
         
         | ILL_Lollipop_proof (lollipop_context, f1, f2, p1) when cut_formula = Lollipop (f1, f2) ->
             let _ = lollipop_context in  (* TODO: Use context for more precise cut elimination *)
             (* Lollipop-cut commutation: move cut above lollipop rule *)
             let cut1 = ILL_Cut_proof (head_ctx, cut_formula, tail_ctx, p1, right_proof) in
             ILL_Lollipop_proof (head_ctx @ tail_ctx, f1, f2, cut1)
         
         | _ -> 
             raise (ILL_Transform_exception "Cannot eliminate cut on left for this proof structure"))
    
    | _ -> 
        raise (ILL_Transform_exception "Can only eliminate cut on cut proofs")

(* Apply cut elimination on the right premise of a cut.
   This commutes the cut with the right premise rule.
   @param cut_proof - Cut proof to transform
   @return ill_proof - Transformed proof *)
let eliminate_cut_right = function
    | ILL_Cut_proof (head_ctx, cut_formula, tail_ctx, left_proof, right_proof) ->
        (match right_proof with
         | ILL_Hypothesis_proof right_sequent when List.mem cut_formula right_sequent.context ->
             (* Hypothesis-cut elimination on right: right uses cut formula in context *)
             (* Create new hypothesis with cut formula removed from context and left context added *)
             let new_context = List.filter (fun f -> f <> cut_formula) right_sequent.context in
             let left_context = match left_proof with
                 | ILL_Hypothesis_proof left_seq -> left_seq.context
                 | _ -> [] in
             let final_context = head_ctx @ left_context @ new_context @ tail_ctx in
             ILL_Hypothesis_proof { context = final_context; goal = right_sequent.goal }
         
         | ILL_Tensor_left_proof (tensor_left_context, f1, f2, premise) when cut_formula = Tensor (f1, f2) ->
             let _ = tensor_left_context in  (* TODO: Use context for more precise cut elimination *)
             (* Tensor-left commutation with cut *)
             let new_premise = ILL_Cut_proof (head_ctx, cut_formula, tail_ctx, left_proof, premise) in
             ILL_Tensor_left_proof (head_ctx @ tail_ctx, f1, f2, new_premise)
         
         | ILL_With_left_1_proof (with_left_context, with_formula, premise) when cut_formula = with_formula ->
             let _ = with_left_context in  (* TODO: Use context for more precise cut elimination *)
             (* With-left-1 commutation with cut *)
             let new_premise = ILL_Cut_proof (head_ctx, cut_formula, tail_ctx, left_proof, premise) in
             ILL_With_left_1_proof (head_ctx @ tail_ctx, with_formula, new_premise)
         
         | ILL_With_left_2_proof (with_left_context, with_formula, premise) when cut_formula = with_formula ->
             let _ = with_left_context in  (* TODO: Use context for more precise cut elimination *)
             (* With-left-2 commutation with cut *)
             let new_premise = ILL_Cut_proof (head_ctx, cut_formula, tail_ctx, left_proof, premise) in
             ILL_With_left_2_proof (head_ctx @ tail_ctx, with_formula, new_premise)
         
         | ILL_Plus_left_proof (plus_left_context, f1, f2, premise1, premise2) when cut_formula = Plus (f1, f2) ->
             let _ = plus_left_context in  (* TODO: Use context for more precise cut elimination *)
             (* Plus-left commutation with cut *)
             let new_premise1 = ILL_Cut_proof (head_ctx, cut_formula, tail_ctx, left_proof, premise1) in
             let new_premise2 = ILL_Cut_proof (head_ctx, cut_formula, tail_ctx, left_proof, premise2) in
             ILL_Plus_left_proof (head_ctx @ tail_ctx, f1, f2, new_premise1, new_premise2)
         
         | ILL_Lollipop_left_proof (lollipop_left_context, f1, f2, premise1, premise2) when cut_formula = Lollipop (f1, f2) ->
             let _ = lollipop_left_context in  (* TODO: Use context for more precise cut elimination *)
             (* Lollipop-left commutation with cut *)
             let new_premise1 = ILL_Cut_proof (head_ctx, cut_formula, tail_ctx, left_proof, premise1) in
             let new_premise2 = ILL_Cut_proof (head_ctx, cut_formula, tail_ctx, left_proof, premise2) in
             ILL_Lollipop_left_proof (head_ctx @ tail_ctx, f1, f2, new_premise1, new_premise2)
         
         | _ -> 
             raise (ILL_Transform_exception "Cannot eliminate cut on right for this proof structure"))
    
    | _ -> 
        raise (ILL_Transform_exception "Can only eliminate cut on cut proofs")

(* Substitute tensor components in a proof context (helper for key-case elimination).
   @param tensor_left_proof - First tensor component proof
   @param tensor_right_proof - Second tensor component proof  
   @param target_premise - Proof to substitute into
   @return ill_proof - Transformed proof *)
let substitute_tensor_in_context tensor_left_proof tensor_right_proof target_premise =
    (* Implement proper tensor substitution by replacing A⊗B with A,B in context *)
    (* This is used in key-case cut elimination for tensor formulas *)
    
    (* Extract the conclusion sequents to understand what we're substituting *)
    let left_sequent = Ill_proof.get_conclusion_sequent tensor_left_proof in
    let right_sequent = Ill_proof.get_conclusion_sequent tensor_right_proof in
    
    (* The cut formula should be A⊗B, where left proves A and right proves B *)
    let left_formula = left_sequent.goal in    (* Should be A *)
    let right_formula = right_sequent.goal in  (* Should be B *)
    
    (* Helper function to substitute tensor A⊗B with A,B in a context *)
    let rec substitute_tensor_in_formula_list formulas =
        match formulas with
        | [] -> []
        | Tensor (f1, f2) :: rest when f1 = left_formula && f2 = right_formula ->
            (* Replace A⊗B with A,B *)
            f1 :: f2 :: substitute_tensor_in_formula_list rest
        | f :: rest ->
            f :: substitute_tensor_in_formula_list rest
    in
    
    (* Helper function to recursively substitute in proof tree structure *)
    let rec substitute_in_proof proof =
        match proof with
        | ILL_Hypothesis_proof sequent ->
            (* Update the context in the sequent *)
            let new_context = substitute_tensor_in_formula_list sequent.context in
            ILL_Hypothesis_proof { sequent with context = new_context }
        
        | ILL_Axiom_proof _ | ILL_One_right_proof | ILL_Top_proof _ ->
            (* These have no premises to update *)
            proof
        
        | ILL_One_left_proof (ctx, p) ->
            let new_ctx = substitute_tensor_in_formula_list ctx in
            let new_p = substitute_in_proof p in
            ILL_One_left_proof (new_ctx, new_p)
        
        | ILL_Tensor_proof (ctx, f1, f2, p1, p2) ->
            let new_ctx = substitute_tensor_in_formula_list ctx in
            let new_p1 = substitute_in_proof p1 in
            let new_p2 = substitute_in_proof p2 in
            ILL_Tensor_proof (new_ctx, f1, f2, new_p1, new_p2)
        
        | ILL_Tensor_left_proof (ctx, f1, f2, p) ->
            let new_ctx = substitute_tensor_in_formula_list ctx in
            let new_p = substitute_in_proof p in
            ILL_Tensor_left_proof (new_ctx, f1, f2, new_p)
        
        | ILL_With_left_1_proof (ctx, f, p) ->
            let new_ctx = substitute_tensor_in_formula_list ctx in
            let new_p = substitute_in_proof p in
            ILL_With_left_1_proof (new_ctx, f, new_p)
        
        | ILL_With_left_2_proof (ctx, f, p) ->
            let new_ctx = substitute_tensor_in_formula_list ctx in
            let new_p = substitute_in_proof p in
            ILL_With_left_2_proof (new_ctx, f, new_p)
        
        | ILL_With_right_proof (ctx, f1, f2, p1, p2) ->
            let new_ctx = substitute_tensor_in_formula_list ctx in
            let new_p1 = substitute_in_proof p1 in
            let new_p2 = substitute_in_proof p2 in
            ILL_With_right_proof (new_ctx, f1, f2, new_p1, new_p2)
        
        | ILL_Plus_left_proof (ctx, f1, f2, p1, p2) ->
            let new_ctx = substitute_tensor_in_formula_list ctx in
            let new_p1 = substitute_in_proof p1 in
            let new_p2 = substitute_in_proof p2 in
            ILL_Plus_left_proof (new_ctx, f1, f2, new_p1, new_p2)
        
        | ILL_Plus_right_1_proof (ctx, f1, f2, p) ->
            let new_ctx = substitute_tensor_in_formula_list ctx in
            let new_p = substitute_in_proof p in
            ILL_Plus_right_1_proof (new_ctx, f1, f2, new_p)
        
        | ILL_Plus_right_2_proof (ctx, f1, f2, p) ->
            let new_ctx = substitute_tensor_in_formula_list ctx in
            let new_p = substitute_in_proof p in
            ILL_Plus_right_2_proof (new_ctx, f1, f2, new_p)
        
        | ILL_Lollipop_proof (ctx, f1, f2, p) ->
            let new_ctx = substitute_tensor_in_formula_list ctx in
            let new_p = substitute_in_proof p in
            ILL_Lollipop_proof (new_ctx, f1, f2, new_p)
        
        | ILL_Lollipop_left_proof (ctx, f1, f2, p1, p2) ->
            let new_ctx = substitute_tensor_in_formula_list ctx in
            let new_p1 = substitute_in_proof p1 in
            let new_p2 = substitute_in_proof p2 in
            ILL_Lollipop_left_proof (new_ctx, f1, f2, new_p1, new_p2)
        
        | ILL_Cut_proof (head_ctx, cut_f, tail_ctx, p1, p2) ->
            let new_head_ctx = substitute_tensor_in_formula_list head_ctx in
            let new_tail_ctx = substitute_tensor_in_formula_list tail_ctx in
            let new_p1 = substitute_in_proof p1 in
            let new_p2 = substitute_in_proof p2 in
            ILL_Cut_proof (new_head_ctx, cut_f, new_tail_ctx, new_p1, new_p2)
        
        (* TODO: Implement proper tensor substitution for exponential rules *)
        | ILL_Weakening_proof (ctx, exp_f, goal_f, p) ->
            let new_ctx = substitute_tensor_in_formula_list ctx in
            let new_p = substitute_in_proof p in
            ILL_Weakening_proof (new_ctx, exp_f, goal_f, new_p)
        
        | ILL_Contraction_proof (ctx, exp_f, goal_f, p) ->
            let new_ctx = substitute_tensor_in_formula_list ctx in
            let new_p = substitute_in_proof p in
            ILL_Contraction_proof (new_ctx, exp_f, goal_f, new_p)
        
        | ILL_Dereliction_proof (ctx, exp_f, goal_f, p) ->
            let new_ctx = substitute_tensor_in_formula_list ctx in
            let new_p = substitute_in_proof p in
            ILL_Dereliction_proof (new_ctx, exp_f, goal_f, new_p)
        
        | ILL_Promotion_proof (ctx, goal_f, p) ->
            let new_ctx = substitute_tensor_in_formula_list ctx in
            let new_p = substitute_in_proof p in
            ILL_Promotion_proof (new_ctx, goal_f, new_p)
    in
    
    substitute_in_proof target_premise

(* Substitute a formula in a proof tree (helper for key-case elimination).
   @param source_formula - Formula to replace
   @param replacement_formula - Formula to replace with
   @param target_proof - Proof to substitute in
   @return ill_proof - Transformed proof *)
let substitute_formula_in_proof source_formula replacement_formula target_proof =
    (* Implement recursive substitution throughout the proof tree structure *)
    (* This function replaces all occurrences of source_formula with replacement_formula *)
    
    (* Helper function to substitute in a single formula *)
    let rec substitute_in_formula formula =
        if formula = source_formula then
            replacement_formula
        else
            match formula with
            | One | Top | Litt _ -> formula  (* Atomic formulas remain unchanged *)
            | Tensor (f1, f2) -> 
                Tensor (substitute_in_formula f1, substitute_in_formula f2)
            | With (f1, f2) -> 
                With (substitute_in_formula f1, substitute_in_formula f2)
            | Plus (f1, f2) -> 
                Plus (substitute_in_formula f1, substitute_in_formula f2)
            | Lollipop (f1, f2) -> 
                Lollipop (substitute_in_formula f1, substitute_in_formula f2)
            | Ofcourse f ->
                (* TODO: Implement proper substitution for exponential formulas *)
                Ofcourse (substitute_in_formula f)
    in
    
    (* Helper function to substitute in a list of formulas (context) *)
    let substitute_in_formula_list formulas =
        List.map substitute_in_formula formulas
    in
    
    (* Helper function to substitute in a sequent *)
    let substitute_in_sequent sequent =
        {
            context = substitute_in_formula_list sequent.context;
            goal = substitute_in_formula sequent.goal;
        }
    in
    
    (* Recursively substitute throughout the proof tree *)
    let rec substitute_in_proof proof =
        match proof with
        | ILL_Hypothesis_proof sequent ->
            ILL_Hypothesis_proof (substitute_in_sequent sequent)
        
        | ILL_Axiom_proof _ ->
            (* Axiom proofs use literal strings, but we should check if the atom matches *)
            proof  (* For now, keep unchanged - full implementation might need atom substitution *)
        
        | ILL_One_right_proof ->
            proof  (* No formulas to substitute *)
        
        | ILL_One_left_proof (ctx, p) ->
            let new_ctx = substitute_in_formula_list ctx in
            let new_p = substitute_in_proof p in
            ILL_One_left_proof (new_ctx, new_p)
        
        | ILL_Top_proof ctx ->
            let new_ctx = substitute_in_formula_list ctx in
            ILL_Top_proof new_ctx
        
        | ILL_Tensor_proof (ctx, f1, f2, p1, p2) ->
            let new_ctx = substitute_in_formula_list ctx in
            let new_f1 = substitute_in_formula f1 in
            let new_f2 = substitute_in_formula f2 in
            let new_p1 = substitute_in_proof p1 in
            let new_p2 = substitute_in_proof p2 in
            ILL_Tensor_proof (new_ctx, new_f1, new_f2, new_p1, new_p2)
        
        | ILL_Tensor_left_proof (ctx, f1, f2, p) ->
            let new_ctx = substitute_in_formula_list ctx in
            let new_f1 = substitute_in_formula f1 in
            let new_f2 = substitute_in_formula f2 in
            let new_p = substitute_in_proof p in
            ILL_Tensor_left_proof (new_ctx, new_f1, new_f2, new_p)
        
        | ILL_With_left_1_proof (ctx, f, p) ->
            let new_ctx = substitute_in_formula_list ctx in
            let new_f = substitute_in_formula f in
            let new_p = substitute_in_proof p in
            ILL_With_left_1_proof (new_ctx, new_f, new_p)
        
        | ILL_With_left_2_proof (ctx, f, p) ->
            let new_ctx = substitute_in_formula_list ctx in
            let new_f = substitute_in_formula f in
            let new_p = substitute_in_proof p in
            ILL_With_left_2_proof (new_ctx, new_f, new_p)
        
        | ILL_With_right_proof (ctx, f1, f2, p1, p2) ->
            let new_ctx = substitute_in_formula_list ctx in
            let new_f1 = substitute_in_formula f1 in
            let new_f2 = substitute_in_formula f2 in
            let new_p1 = substitute_in_proof p1 in
            let new_p2 = substitute_in_proof p2 in
            ILL_With_right_proof (new_ctx, new_f1, new_f2, new_p1, new_p2)
        
        | ILL_Plus_left_proof (ctx, f1, f2, p1, p2) ->
            let new_ctx = substitute_in_formula_list ctx in
            let new_f1 = substitute_in_formula f1 in
            let new_f2 = substitute_in_formula f2 in
            let new_p1 = substitute_in_proof p1 in
            let new_p2 = substitute_in_proof p2 in
            ILL_Plus_left_proof (new_ctx, new_f1, new_f2, new_p1, new_p2)
        
        | ILL_Plus_right_1_proof (ctx, f1, f2, p) ->
            let new_ctx = substitute_in_formula_list ctx in
            let new_f1 = substitute_in_formula f1 in
            let new_f2 = substitute_in_formula f2 in
            let new_p = substitute_in_proof p in
            ILL_Plus_right_1_proof (new_ctx, new_f1, new_f2, new_p)
        
        | ILL_Plus_right_2_proof (ctx, f1, f2, p) ->
            let new_ctx = substitute_in_formula_list ctx in
            let new_f1 = substitute_in_formula f1 in
            let new_f2 = substitute_in_formula f2 in
            let new_p = substitute_in_proof p in
            ILL_Plus_right_2_proof (new_ctx, new_f1, new_f2, new_p)
        
        | ILL_Lollipop_proof (ctx, f1, f2, p) ->
            let new_ctx = substitute_in_formula_list ctx in
            let new_f1 = substitute_in_formula f1 in
            let new_f2 = substitute_in_formula f2 in
            let new_p = substitute_in_proof p in
            ILL_Lollipop_proof (new_ctx, new_f1, new_f2, new_p)
        
        | ILL_Lollipop_left_proof (ctx, f1, f2, p1, p2) ->
            let new_ctx = substitute_in_formula_list ctx in
            let new_f1 = substitute_in_formula f1 in
            let new_f2 = substitute_in_formula f2 in
            let new_p1 = substitute_in_proof p1 in
            let new_p2 = substitute_in_proof p2 in
            ILL_Lollipop_left_proof (new_ctx, new_f1, new_f2, new_p1, new_p2)
        
        | ILL_Cut_proof (head_ctx, cut_f, tail_ctx, p1, p2) ->
            let new_head_ctx = substitute_in_formula_list head_ctx in
            let new_tail_ctx = substitute_in_formula_list tail_ctx in
            let new_cut_f = substitute_in_formula cut_f in
            let new_p1 = substitute_in_proof p1 in
            let new_p2 = substitute_in_proof p2 in
            ILL_Cut_proof (new_head_ctx, new_cut_f, new_tail_ctx, new_p1, new_p2)
        
        (* TODO: Implement proper substitution for exponential rules *)
        | ILL_Weakening_proof (ctx, exp_f, goal_f, p) ->
            let new_ctx = substitute_in_formula_list ctx in
            let new_exp_f = substitute_in_formula exp_f in
            let new_goal_f = substitute_in_formula goal_f in
            let new_p = substitute_in_proof p in
            ILL_Weakening_proof (new_ctx, new_exp_f, new_goal_f, new_p)
        
        | ILL_Contraction_proof (ctx, exp_f, goal_f, p) ->
            let new_ctx = substitute_in_formula_list ctx in
            let new_exp_f = substitute_in_formula exp_f in
            let new_goal_f = substitute_in_formula goal_f in
            let new_p = substitute_in_proof p in
            ILL_Contraction_proof (new_ctx, new_exp_f, new_goal_f, new_p)
        
        | ILL_Dereliction_proof (ctx, exp_f, goal_f, p) ->
            let new_ctx = substitute_in_formula_list ctx in
            let new_exp_f = substitute_in_formula exp_f in
            let new_goal_f = substitute_in_formula goal_f in
            let new_p = substitute_in_proof p in
            ILL_Dereliction_proof (new_ctx, new_exp_f, new_goal_f, new_p)
        
        | ILL_Promotion_proof (ctx, goal_f, p) ->
            let new_ctx = substitute_in_formula_list ctx in
            let new_goal_f = substitute_in_formula goal_f in
            let new_p = substitute_in_proof p in
            ILL_Promotion_proof (new_ctx, new_goal_f, new_p)
    in
    
    substitute_in_proof target_proof

(* Apply key-case cut elimination.
   This handles cuts where the cut formula is principal in both premises.
   @param cut_proof - Cut proof to transform
   @return ill_proof - Transformed proof *)
let eliminate_cut_key_case = function
    | ILL_Cut_proof (head_ctx, cut_formula, tail_ctx, left_proof, right_proof) ->
        (match left_proof, right_proof with
         (* Tensor/Tensor-left key case *)
         | ILL_Tensor_proof (_, f1, f2, p1, p2), ILL_Tensor_left_proof (_, g1, g2, premise) 
             when cut_formula = Tensor (f1, f2) && f1 = g1 && f2 = g2 ->
             (* Replace tensor construction with direct proof *)
             let subst_proof = substitute_tensor_in_context p1 p2 premise in
             subst_proof
         
         (* With/With-left key cases *)
         | ILL_With_right_proof (with_context, f1, f2, left_branch_proof, right_branch_proof), ILL_With_left_1_proof (with_left_context, with_formula, premise) 
             when cut_formula = With (f1, f2) && With (f1, f2) = with_formula ->
             let _ = (with_context, right_branch_proof, with_left_context) in  (* TODO: Use for context reconstruction *)
             (* Use first branch of with-right *)
             let new_premise = substitute_formula_in_proof cut_formula f1 premise in
             ILL_Cut_proof (head_ctx, f1, tail_ctx, left_branch_proof, new_premise)
         
         | ILL_With_right_proof (with_context, f1, f2, left_branch_proof, right_branch_proof), ILL_With_left_2_proof (with_left_context, with_formula, premise) 
             when cut_formula = With (f1, f2) && With (f1, f2) = with_formula ->
             let _ = (with_context, left_branch_proof, with_left_context) in  (* TODO: Use for context reconstruction *)
             (* Use second branch of with-right *)
             let new_premise = substitute_formula_in_proof cut_formula f2 premise in
             ILL_Cut_proof (head_ctx, f2, tail_ctx, right_branch_proof, new_premise)
         
         (* Plus/Plus-left key cases *)
         | ILL_Plus_right_1_proof (plus_right_context, f1, f2, first_branch_proof), ILL_Plus_left_proof (plus_left_context, g1, g2, left_premise, right_premise) 
             when cut_formula = Plus (f1, f2) && f1 = g1 && f2 = g2 ->
             let _ = (plus_right_context, plus_left_context, right_premise) in  (* TODO: Use for context reconstruction *)
             (* Use first branch of plus-left *)
             let new_premise = substitute_formula_in_proof cut_formula f1 left_premise in
             ILL_Cut_proof (head_ctx, f1, tail_ctx, first_branch_proof, new_premise)
         
         | ILL_Plus_right_2_proof (plus_right_context, f1, f2, second_branch_proof), ILL_Plus_left_proof (plus_left_context, g1, g2, left_premise, right_premise) 
             when cut_formula = Plus (f1, f2) && f1 = g1 && f2 = g2 ->
             let _ = (plus_right_context, plus_left_context, left_premise) in  (* TODO: Use for context reconstruction *)
             (* Use second branch of plus-left *)
             let new_premise = substitute_formula_in_proof cut_formula f2 right_premise in
             ILL_Cut_proof (head_ctx, f2, tail_ctx, second_branch_proof, new_premise)
         
         (* Lollipop/Lollipop-left key case *)
         | ILL_Lollipop_proof (_, f1, f2, p1), ILL_Lollipop_left_proof (_, g1, g2, premise1, premise2) 
             when cut_formula = Lollipop (f1, f2) && f1 = g1 && f2 = g2 ->
             (* Connect lollipop premises *)
             let cut1 = ILL_Cut_proof (head_ctx, f1, [], premise1, p1) in
             ILL_Cut_proof (head_ctx, f2, tail_ctx, cut1, premise2)
         
         (* Hypothesis-hypothesis key case: both sides are incomplete proofs *)
         | ILL_Hypothesis_proof left_seq, ILL_Hypothesis_proof right_seq 
             when left_seq.goal = cut_formula && List.mem cut_formula right_seq.context ->
             (* Replace ONE occurrence of cut_formula in right context with left context *)
             let rec substitute_first target replacement = function
                 | [] -> []
                 | h :: t when h = target -> replacement @ t
                 | h :: t -> h :: substitute_first target replacement t
             in
             (* The right context already includes the cut formula, so just substitute within it *)
             let final_context = substitute_first cut_formula left_seq.context right_seq.context in
             ILL_Hypothesis_proof { context = final_context; goal = right_seq.goal }
         
         | _ -> 
             raise (ILL_Transform_exception "No key-case available for this cut"))
    
    | _ -> 
        raise (ILL_Transform_exception "Can only eliminate key-case on cut proofs")


(* Apply full cut elimination to completely remove a cut.
   @param cut_proof - Cut proof to eliminate
   @return ill_proof - Proof with cut eliminated *)
let eliminate_cut_full cut_proof =
    match cut_proof with
    | ILL_Cut_proof (_, _, _, _, _) ->
        (* Try different elimination strategies in order *)
        (try eliminate_cut_key_case cut_proof
         with ILL_Transform_exception _ ->
         try eliminate_cut_left cut_proof
         with ILL_Transform_exception _ ->
         try eliminate_cut_right cut_proof
         with ILL_Transform_exception _ ->
         raise (ILL_Transform_exception "Cannot eliminate this cut"))
    | _ -> 
        raise (ILL_Transform_exception "Can only fully eliminate cuts")

(* Apply cut elimination recursively throughout a proof tree.
   @param proof - Proof tree to process
   @return ill_proof - Proof with all cuts eliminated *)
let rec eliminate_all_cuts proof =
    let new_proof = match proof with
        | ILL_Cut_proof (_, _, _, _, _) -> eliminate_cut_full proof
        | _ -> proof
    in
    set_premises new_proof (List.map eliminate_all_cuts (get_premises new_proof))

(* MAIN TRANSFORMATION APPLICATION *)

(* Apply a transformation to an ILL proof tree.
   @param transform_req - Transformation to apply
   @param proof - Proof tree to transform
   @return ill_proof - Transformed proof tree *)
let apply_transformation transform_req proof =
    Printf.eprintf "[ILL-TRANSFORM] Applying ILL transformation: %s\n%!" (Ill_transform_request.to_string transform_req);
    match transform_req with
    | ILL_Expand_axiom -> 
        Printf.eprintf "[ILL-TRANSFORM] Processing expand_axiom\n%!";
        let result = expand_axiom_on_proof proof in
        Printf.eprintf "[ILL-TRANSFORM] Expand_axiom completed successfully\n%!";
        result
    | ILL_Expand_axiom_full -> 
        Printf.eprintf "[ILL-TRANSFORM] Processing expand_axiom_full\n%!";
        let result = expand_axiom_full proof in
        Printf.eprintf "[ILL-TRANSFORM] Expand_axiom_full completed successfully\n%!";
        result
    | ILL_Eliminate_cut_left -> 
        Printf.eprintf "[ILL-TRANSFORM] Processing eliminate_cut_left\n%!";
        let result = eliminate_cut_left proof in
        Printf.eprintf "[ILL-TRANSFORM] Eliminate_cut_left completed successfully\n%!";
        result
    | ILL_Eliminate_cut_key_case -> 
        Printf.eprintf "[ILL-TRANSFORM] Processing eliminate_cut_key_case\n%!";
        let result = eliminate_cut_key_case proof in
        Printf.eprintf "[ILL-TRANSFORM] Eliminate_cut_key_case completed successfully\n%!";
        result
    | ILL_Eliminate_cut_right -> 
        Printf.eprintf "[ILL-TRANSFORM] Processing eliminate_cut_right\n%!";
        let result = eliminate_cut_right proof in
        Printf.eprintf "[ILL-TRANSFORM] Eliminate_cut_right completed successfully\n%!";
        result
    | ILL_Eliminate_cut_full -> 
        Printf.eprintf "[ILL-TRANSFORM] Processing eliminate_cut_full\n%!";
        let result = eliminate_cut_full proof in
        Printf.eprintf "[ILL-TRANSFORM] Eliminate_cut_full completed successfully\n%!";
        result
    | ILL_Eliminate_all_cuts -> 
        Printf.eprintf "[ILL-TRANSFORM] Processing eliminate_all_cuts\n%!";
        let result = eliminate_all_cuts proof in
        Printf.eprintf "[ILL-TRANSFORM] Eliminate_all_cuts completed successfully\n%!";
        result
    | ILL_Simplify -> 
        Printf.eprintf "[ILL-TRANSFORM] Processing simplify\n%!";
        (* Implement proof simplification: remove redundant rules and normalize structure *)
        let rec simplify_proof proof =
            Printf.eprintf "[ILL-TRANSFORM] Simplifying proof node\n%!";
            match proof with
            (* Remove redundant cut-axiom combinations *)
            | ILL_Cut_proof (_, cut_formula, _, ILL_Axiom_proof atom, right_proof) 
                when cut_formula = Litt atom ->
                Printf.eprintf "[ILL-TRANSFORM] Removing redundant cut-axiom for atom: %s\n%!" atom;
                simplify_proof right_proof
            
            (* Remove redundant cut-one combinations *)
            | ILL_Cut_proof (_, One, _, ILL_One_right_proof, right_proof) ->
                Printf.eprintf "[ILL-TRANSFORM] Removing redundant cut-one combination\n%!";
                simplify_proof right_proof
            
            (* Simplify nested cuts with same formula *)
            | ILL_Cut_proof (head_ctx1, f1, tail_ctx1, 
                ILL_Cut_proof (head_ctx2, f2, tail_ctx2, p1, p2), p3) 
                when f1 = f2 && head_ctx1 = head_ctx2 && tail_ctx1 = tail_ctx2 ->
                Printf.eprintf "[ILL-TRANSFORM] Flattening nested cuts with same formula\n%!";
                (* Flatten nested cuts *)
                let simplified_inner = ILL_Cut_proof (head_ctx2, f2, tail_ctx2, simplify_proof p1, simplify_proof p2) in
                simplify_proof (ILL_Cut_proof (head_ctx1, f1, tail_ctx1, simplified_inner, simplify_proof p3))
            
            (* Recursively simplify all premises *)
            | _ -> 
                let premises = get_premises proof in
                Printf.eprintf "[ILL-TRANSFORM] Recursively simplifying %d premises\n%!" (List.length premises);
                let simplified_premises = List.map simplify_proof premises in
                set_premises proof simplified_premises
        in
        let result = simplify_proof proof in
        Printf.eprintf "[ILL-TRANSFORM] Simplify completed successfully\n%!";
        result
    | ILL_Substitute (alias, replacement_formula) -> 
        Printf.eprintf "[ILL-TRANSFORM] Processing substitute for alias: %s\n%!" alias;
        (* Implement formula substitution: replace all occurrences of alias with replacement_formula *)
        let source_formula = Litt alias in
        let result = substitute_formula_in_proof source_formula replacement_formula proof in
        Printf.eprintf "[ILL-TRANSFORM] Substitute completed successfully\n%!";
        result
    | ILL_Apply_reversible_first _ -> 
        Printf.eprintf "[ILL-TRANSFORM] Processing apply_reversible_first\n%!";
        (* Implement reversible rule application: apply deterministic rules first *)
        let rec apply_reversible_rules proof =
            Printf.eprintf "[ILL-TRANSFORM] Applying reversible rules to proof node\n%!";
            match proof with
            | ILL_Hypothesis_proof sequent ->
                (* Try to apply reversible rules based on the goal and context *)
                (match sequent.goal with
                | One -> 
                    Printf.eprintf "[ILL-TRANSFORM] Applying reversible One rule\n%!";
                    (* One rule is always reversible *)
                    ILL_One_right_proof
                | Top ->
                    Printf.eprintf "[ILL-TRANSFORM] Applying reversible Top rule\n%!";
                    (* Top rule is always reversible *)
                    ILL_Top_proof sequent.context
                | Litt atom when List.mem (Litt atom) sequent.context ->
                    Printf.eprintf "[ILL-TRANSFORM] Applying reversible Axiom rule for atom: %s\n%!" atom;
                    (* Axiom rule is reversible when goal appears in context *)
                    ILL_Axiom_proof atom
                | Lollipop (f1, f2) ->
                    Printf.eprintf "[ILL-TRANSFORM] Applying reversible Lollipop rule\n%!";
                    (* Lollipop right rule is reversible *)
                    let new_context = f1 :: sequent.context in
                    let new_sequent = { context = new_context; goal = f2 } in
                    let premise = ILL_Hypothesis_proof new_sequent in
                    ILL_Lollipop_proof (sequent.context, f1, f2, apply_reversible_rules premise)
                | _ ->
                    (* For non-reversible goals, try reversible left rules on context *)
                    let rec try_left_rules ctx acc =
                        match ctx with
                        | [] -> ILL_Hypothesis_proof sequent  (* No reversible rules found *)
                        | Tensor (f1, f2) :: rest ->
                            Printf.eprintf "[ILL-TRANSFORM] Applying reversible Tensor left rule\n%!";
                            (* Tensor left is reversible *)
                            let new_context = acc @ [f1; f2] @ rest in
                            let new_sequent = { context = new_context; goal = sequent.goal } in
                            let premise = ILL_Hypothesis_proof new_sequent in
                            ILL_Tensor_left_proof (sequent.context, f1, f2, apply_reversible_rules premise)
                        | Lollipop (f1, f2) :: rest ->
                            (* Lollipop left has two premises - not fully reversible, skip for now *)
                            try_left_rules rest (Lollipop (f1, f2) :: acc)
                        | f :: rest ->
                            try_left_rules rest (f :: acc)
                    in
                    try_left_rules sequent.context [])
            | _ ->
                (* For non-hypothesis proofs, recursively apply to premises *)
                let simplified_premises = List.map apply_reversible_rules (get_premises proof) in
                set_premises proof simplified_premises
        in
        let result = apply_reversible_rules proof in
        Printf.eprintf "[ILL-TRANSFORM] Apply_reversible_first completed successfully\n%!";
        result

(* Check if any cuts in the proof tree can be eliminated.
   @param proof - Proof tree to check
   @return bool - True if cuts can be eliminated *)
let rec has_cut_that_can_be_eliminated proof =
    let transform_options = get_transform_options proof in
    if List.mem_assoc ILL_Eliminate_cut_full transform_options
        && let enabled, _ = List.assoc ILL_Eliminate_cut_full transform_options in enabled
    then true
    else List.exists has_cut_that_can_be_eliminated (get_premises proof)

(* CONTEXT MANIPULATION UTILITIES *)

(* Split a context at a specific position.
   @param ctx - Formula list to split
   @param position - 0-based index to split at
   @return (left_part, right_part) - Split context
*)
let split_context_at_position ctx position =
    let rec split acc n lst =
        match n, lst with
        | 0, rest -> (List.rev acc, rest)
        | n, h :: t when n > 0 -> split (h :: acc) (n - 1) t
        | _ -> (List.rev acc, lst)
    in
    split [] position ctx

(* Merge two contexts into one.
   @param ctx1 - First context
   @param ctx2 - Second context  
   @return formula list - Combined context
*)
let merge_contexts ctx1 ctx2 = ctx1 @ ctx2

(* Remove a specific formula from a context.
   @param formula - Formula to remove
   @param ctx - Context to remove from
   @return formula list - Context with formula removed (first occurrence)
*)
let remove_formula_from_context formula ctx =
    let rec remove_first = function
        | [] -> []
        | f :: rest when f = formula -> rest
        | f :: rest -> f :: remove_first rest
    in
    remove_first ctx

(* Insert a formula at a specific position in a context.
   @param formula - Formula to insert
   @param position - 0-based position to insert at
   @param ctx - Context to insert into
   @return formula list - Context with formula inserted
*)
let insert_formula_in_context formula position ctx =
    let rec insert acc n f lst =
        match n, lst with
        | 0, rest -> List.rev acc @ (f :: rest)
        | n, h :: t when n > 0 -> insert (h :: acc) (n - 1) f t
        | _, [] -> List.rev acc @ [f]  (* Insert at end if position beyond list *)
        | _ -> List.rev acc @ [f]  (* Fallback case *)
    in
    insert [] position formula ctx

(* Find all positions of a formula in a context.
   @param formula - Formula to find
   @param ctx - Context to search in
   @return int list - List of 0-based positions where formula occurs
*)
let find_formula_positions formula ctx =
    let rec find_positions acc pos = function
        | [] -> List.rev acc
        | f :: rest when f = formula -> find_positions (pos :: acc) (pos + 1) rest
        | _ :: rest -> find_positions acc (pos + 1) rest
    in
    find_positions [] 0 ctx

(* Check if a context contains a specific formula.
   @param formula - Formula to check for
   @param ctx - Context to check
   @return bool - True if formula is present
*)
let context_contains_formula formula ctx =
    List.mem formula ctx

(* Count occurrences of a formula in a context.
   @param formula - Formula to count
   @param ctx - Context to count in
   @return int - Number of occurrences
*)
let count_formula_in_context formula ctx =
    List.fold_left (fun acc f -> if f = formula then acc + 1 else acc) 0 ctx

(* Replace all occurrences of one formula with another in a context.
   @param old_formula - Formula to replace
   @param new_formula - Formula to replace with
   @param ctx - Context to update
   @return formula list - Updated context
*)
let replace_formula_in_context old_formula new_formula ctx =
    List.map (fun f -> if f = old_formula then new_formula else f) ctx

(* API FUNCTIONS FOR WEB SERVER *)

(* Get ILL proof transformation options from JSON request.
   This is the main API endpoint for the frontend to query available transformations.
   @param request_as_json - JSON request from frontend
   @return (bool * Yojson.Basic.t) - (success, response) *)
let get_ill_proof_transformation_options request_as_json =
    Printf.eprintf "[ILL-TRANSFORM] Getting ILL proof transformation options\n%!";
    try 
        (* Parse ILL proof from JSON request - same format as classical LL *)
        let proof_json = Request_utils.get_key request_as_json "proof" in
        Printf.eprintf "[ILL-TRANSFORM] Extracted proof JSON from request\n%!";
        let ill_proof = Ill_proof.from_json proof_json in
        Printf.eprintf "[ILL-TRANSFORM] Parsed ILL proof successfully\n%!";
        
        (* Generate transformation options for the real proof *)
        let transform_options_json = get_transform_options_as_json ill_proof in
        Printf.eprintf "[ILL-TRANSFORM] Generated transformation options\n%!";
        let can_eliminate_all_cuts = has_cut_that_can_be_eliminated ill_proof in
        Printf.eprintf "[ILL-TRANSFORM] Can eliminate all cuts: %b\n%!" can_eliminate_all_cuts;
        let can_simplify = true in (* Basic simplification is always available for now *)
        Printf.eprintf "[ILL-TRANSFORM] Can simplify: %b\n%!" can_simplify;
        
        (* Include the original proof along with transformation options *)
        let proof_json = Ill_proof.to_json ill_proof in
        let proof_with_options = match proof_json with
            | `Assoc proof_fields -> 
                `Assoc (proof_fields @ transform_options_json)
            | _ -> 
                `Assoc (["proof", proof_json] @ transform_options_json)
        in
        
        Printf.eprintf "[ILL-TRANSFORM] Returning successful ILL transformation options\n%!";
        true, `Assoc [
            "illProofWithTransformationOptions", proof_with_options;
            "canSimplify", `Bool can_simplify;
            "canEliminateAllCuts", `Bool can_eliminate_all_cuts]
    with 
    | Request_utils.Bad_request_exception m -> 
        Printf.eprintf "[ILL-TRANSFORM ERROR] Bad request: %s\n%!" m;
        false, `String ("Bad request: " ^ m)
    | ILL_Transform_exception m -> 
        Printf.eprintf "[ILL-TRANSFORM ERROR] ILL Transform exception: %s\n%!" m;
        false, `String ("ILL Transform exception: " ^ m)
    | ILL_Proof_Exception (_, m) -> 
        Printf.eprintf "[ILL-TRANSFORM ERROR] ILL Proof exception: %s\n%!" m;
        false, `String ("ILL Proof exception: " ^ m)
    | Yojson.Basic.Util.Type_error (msg, _) -> 
        Printf.eprintf "[ILL-TRANSFORM ERROR] JSON parsing error: %s\n%!" msg;
        false, `String ("JSON parsing error: " ^ msg)
    | _ -> 
        Printf.eprintf "[ILL-TRANSFORM ERROR] Unknown error in ILL transformation options\n%!";
        false, `String "Unknown error in ILL transformation options"

(* Apply ILL transformation from JSON request.
   This is the main API endpoint for applying transformations to ILL proofs.
   @param request_as_json - JSON request from frontend with transformation details
   @return (bool * Yojson.Basic.t) - (success, response) *)
let apply_ill_transformation request_as_json =
    Printf.eprintf "[ILL-TRANSFORM] Applying ILL transformation from request\n%!";
    try
        (* Parse ILL proof and transformation request from JSON *)
        let transform_request_as_json = Request_utils.get_key request_as_json "transformRequest" in
        Printf.eprintf "[ILL-TRANSFORM] Extracted transform request from JSON\n%!";
        let transform_request = Ill_transform_request.from_json transform_request_as_json in
        Printf.eprintf "[ILL-TRANSFORM] Parsed transformation request: %s\n%!" (Ill_transform_request.to_string transform_request);
        
        (* Parse the actual ILL proof from the request - same format as classical LL *)
        let proof_json = Request_utils.get_key request_as_json "proof" in
        Printf.eprintf "[ILL-TRANSFORM] Extracted proof JSON from request\n%!";
        let original_proof = Ill_proof.from_json proof_json in
        Printf.eprintf "[ILL-TRANSFORM] Parsed original ILL proof successfully\n%!";
        
        (* Apply the transformation *)
        let transformed_proof = apply_transformation transform_request original_proof in
        Printf.eprintf "[ILL-TRANSFORM] Applied transformation successfully\n%!";
        
        (* Convert ILL proof back to JSON format *)
        let transformed_proof_json = Ill_proof.to_json transformed_proof in
        Printf.eprintf "[ILL-TRANSFORM] Converted transformed proof to JSON\n%!";
        
        Printf.eprintf "[ILL-TRANSFORM] Returning successful transformation result\n%!";
        true, `Assoc [
            "illProof", transformed_proof_json;
            "transformationApplied", `String (Ill_transform_request.to_string transform_request)]
    with
    | Request_utils.Bad_request_exception m -> 
        Printf.eprintf "[ILL-TRANSFORM ERROR] Bad request: %s\n%!" m;
        false, `String ("Bad request: " ^ m)
    | Ill_transform_request.ILL_Transform_Json_Exception m -> 
        Printf.eprintf "[ILL-TRANSFORM ERROR] Bad ILL transformation request: %s\n%!" m;
        false, `String ("Bad ILL transformation request: " ^ m)
    | ILL_Transform_exception m -> 
        Printf.eprintf "[ILL-TRANSFORM ERROR] ILL Transform exception: %s\n%!" m;
        false, `String ("ILL Transform exception: " ^ m)
    | ILL_Proof_Exception (_, m) -> 
        Printf.eprintf "[ILL-TRANSFORM ERROR] ILL Proof exception: %s\n%!" m;
        false, `String ("ILL Proof exception: " ^ m)
    | ILL_Pedagogic_exception m -> 
        Printf.eprintf "[ILL-TRANSFORM ERROR] ILL Pedagogic exception: %s\n%!" m;
        true, `Assoc ["error_message", `String m]
    | Yojson.Basic.Util.Type_error (msg, _) -> 
        Printf.eprintf "[ILL-TRANSFORM ERROR] JSON parsing error: %s\n%!" msg;
        false, `String ("JSON parsing error: " ^ msg)
    | _ -> 
        Printf.eprintf "[ILL-TRANSFORM ERROR] Unknown error in ILL transformation\n%!";
        false, `String "Unknown error in ILL transformation options"