(*
#load "ListMore.cmo"
#load "Fixpoint.cmo";;
#load "Prop.cmo";;
#load "ProcImp.cmo";;
#load "PDS.cmo";;
#load "APDS.cmo";;
#load "AMA.cmo";;
#load "SCTPLB.cmo";;
*)
open ListMore;;
open Fixpoint;;
open Prop;;
open ProcImp;;
open PDS;;
open APDS;;
open AMA;;
open SCTPLB;;

(* step 1: annotate CFG with ordered control point names *)
let annotated_ast_of_program
    ((ProcImp.AST.Program fundef_list) : ProcImp.AST.t)
    =
  let counter = ref 0 in
  let annotated_ast =
    let annotated_ast_of_fun (ProcImp.AST.FunDef (ProcImp.AST.Identifier id_name, identifierlist, s)) =
      let () = counter := 0 in
      let rec annotated_ast_of_stmt (s : ProcImp.AST.statement) =
	let control_point_name () : (string * int) PDS.control_point =
	  let () = counter := !counter + 1 in
	  (id_name, !counter) in
	match s with
	  | ProcImp.AST.Skip                   -> ProcImp.AST.AnnotatedSkip (control_point_name ())
	  | ProcImp.AST.Halt	                  -> ProcImp.AST.AnnotatedHalt (control_point_name ())
	  | ProcImp.AST.Sequence (s1, s2)      -> 
	    let annotated_ast_of_s1 = annotated_ast_of_stmt s1 in
	    let annotated_ast_of_s2 = annotated_ast_of_stmt s2 in
	    ProcImp.AST.AnnotatedSequence (annotated_ast_of_s1, annotated_ast_of_s2)
	  | ProcImp.AST.Assignment (id, e)     -> ProcImp.AST.AnnotatedAssignment (control_point_name (), id, e)
	  | ProcImp.AST.FunCallStmt (id, el)   -> ProcImp.AST.AnnotatedFunCallStmt (control_point_name (), id, el)
	  | ProcImp.AST.IfThenElse (e, s1, s2) ->
	    let cpn = control_point_name () in
	    let annotated_ast_of_s1 = annotated_ast_of_stmt s1 in
	    let annotated_ast_of_s2 = annotated_ast_of_stmt s2 in
	    ProcImp.AST.AnnotatedIfThenElse (cpn, e, annotated_ast_of_s1, annotated_ast_of_s2)
	  | ProcImp.AST.While (e, s)           ->
	    let cpn = control_point_name () in
	    let annotated_ast_of_s = annotated_ast_of_stmt s in
	    ProcImp.AST.AnnotatedWhile (cpn, e, annotated_ast_of_s)
	  | ProcImp.AST.Return e               ->
	    let cpn = control_point_name () in
	    ProcImp.AST.AnnotatedReturn (cpn, e)
      in annotated_ast_of_stmt (ProcImp.AST.sequence_normal_form s) (* sequence normal form here*)
    in List.map
    (fun fd ->
      let () = counter := 0 in
      (match fd with ProcImp.AST.FunDef (ProcImp.AST.Identifier id_name, _, _) -> id_name,
	annotated_ast_of_fun fd))
    fundef_list
  in annotated_ast
;;

(* liste des fonctions utilisées dans le programme *)
(* à changer pour que ça se fasse en fonction du programme... *)
(* let gamma_alphabet = [ProcImp.AST.Identifier "main"] *)

let stack_alphabet_of_procimp_program ((ProcImp.AST.Program fundef_list) : ProcImp.AST.t) =
  List.map (fun (ProcImp.AST.FunDef (fun_name, _, _)) -> fun_name) fundef_list
;;


(* step 2: give model transitions wrt tokens of AST *)
let transitions_of_annotated_functions
    l
    gamma_alphabet
    : ((ProcImp.AST.identifier, (string * int)) PDS.transition) list
    =
  let out_points_of_fun (fun_name : string) : (string * int) PDS.control_point list =
    let rec aux annotated_ast =  match annotated_ast with
    | ProcImp.AST.AnnotatedSequence (as1, as2)         -> (aux as1) @ (aux as2)
    | ProcImp.AST.AnnotatedIfThenElse (_, _, as1, as2) -> (aux as1) @ (aux as2)
    | ProcImp.AST.AnnotatedWhile (_, _, as1)           -> aux as1
    | ProcImp.AST.AnnotatedReturn (cpn, _)             -> [cpn]
    | _                                           -> [] in
    aux (List.assoc fun_name l) in
  let rec first_control_point_names_of_annotated_stmt an_s : (string * int) PDS.control_point = match an_s with
    | ProcImp.AST.AnnotatedSkip (cpn)                -> cpn
    | ProcImp.AST.AnnotatedHalt (cpn)                -> cpn
    | ProcImp.AST.AnnotatedSequence (as1, as2)       -> first_control_point_names_of_annotated_stmt as1
    | ProcImp.AST.AnnotatedAssignment (cpn, _, _)    -> cpn 	
    | ProcImp.AST.AnnotatedFunCallStmt (cpn, _, _)   -> cpn
    | ProcImp.AST.AnnotatedIfThenElse (cpn, _, _, _) -> cpn
    | ProcImp.AST.AnnotatedWhile (cpn, _, as1)       -> cpn
    | ProcImp.AST.AnnotatedReturn (cpn, _)           -> cpn
  and last_control_point_names_of_annotated_stmt an_s : (string * int) PDS.control_point = match an_s with
    | ProcImp.AST.AnnotatedSkip (cpn)                  -> cpn
    | ProcImp.AST.AnnotatedHalt (cpn)                  -> cpn
    | ProcImp.AST.AnnotatedSequence (as1, as2)         -> last_control_point_names_of_annotated_stmt as2
    | ProcImp.AST.AnnotatedAssignment (cpn, _, _)      -> cpn 	
    | ProcImp.AST.AnnotatedFunCallStmt (cpn, _, _)     -> cpn
    | ProcImp.AST.AnnotatedIfThenElse (cpn, _, _, a_s) -> last_control_point_names_of_annotated_stmt a_s
    | ProcImp.AST.AnnotatedWhile (cpn, _, as1)         -> last_control_point_names_of_annotated_stmt as1
    | ProcImp.AST.AnnotatedReturn (cpn, _)             -> cpn
  in
  let rec transitions_of_fun (fun_name, fun_annotated_ast) = match fun_annotated_ast with
    | ProcImp.AST.AnnotatedSequence (ProcImp.AST.AnnotatedSequence _, _) ->
      failwith "Not in ProcImp-sequence normal form"
    | ProcImp.AST.AnnotatedSequence (ProcImp.AST.AnnotatedIfThenElse (cpn, e, as1, as2), as3) ->
      (List.map
	 (fun gamma ->
	   (cpn,
	    gamma,
	    [gamma],
	    first_control_point_names_of_annotated_stmt as1))
	 gamma_alphabet)
      @ (List.map
	 (fun gamma ->
	   (cpn,
	    gamma,
	    [gamma],
	    first_control_point_names_of_annotated_stmt as2))
	 gamma_alphabet)
      @ (List.map
	 (fun gamma ->
	   (last_control_point_names_of_annotated_stmt as1,
	    gamma,
	    [gamma],
	    first_control_point_names_of_annotated_stmt as3))
	 gamma_alphabet)
      @ (List.map
	 (fun gamma ->
	   (last_control_point_names_of_annotated_stmt as2,
	    gamma,
	    [gamma],
	    first_control_point_names_of_annotated_stmt as3))
	 gamma_alphabet)
      @ transitions_of_fun (fun_name, as1)
      @ transitions_of_fun (fun_name, as2)
      @ transitions_of_fun (fun_name, as3)
    | ProcImp.AST.AnnotatedSequence (ProcImp.AST.AnnotatedWhile (cpn, e, as1), as2) ->
      (List.map
	 (fun gamma ->
	   (cpn,
	    gamma,
	    [gamma],
	    first_control_point_names_of_annotated_stmt as1))
	 gamma_alphabet)
      @ (List.map
	 (fun gamma ->
	   (cpn,
	    gamma,
	    [gamma],
	    first_control_point_names_of_annotated_stmt as2))
	 gamma_alphabet)
      @ (List.map
	 (fun gamma ->
	   (last_control_point_names_of_annotated_stmt as1,
	    gamma,
	    [gamma],
	    cpn))
	 gamma_alphabet)
      @ transitions_of_fun (fun_name, as1)
      @ transitions_of_fun (fun_name, as2)
    | ProcImp.AST.AnnotatedSequence (ProcImp.AST.AnnotatedFunCallStmt ((current_fun_name, current_fun_cp_number), ProcImp.AST.Identifier x, args), as2) ->
(*      let () = print_endline "goes here!" in   *)
      (List.map
	 (fun gamma ->
	   ((current_fun_name, current_fun_cp_number),
	    gamma,
	    [ProcImp.AST.Identifier current_fun_name ; gamma], (* BIG BUG : c'est pas la destination qu'il faut mettre mais la fonction courante ! *)
	    (x, 1)))
	 gamma_alphabet)
      @ List.flatten (
	List.map
	  (fun cpn -> List.map
	    (fun gamma ->
	      (cpn,
	       gamma,
	       [], (* epsilon *)
	       first_control_point_names_of_annotated_stmt as2))
	     gamma_alphabet)
	  (out_points_of_fun x))

      (** (as1 ; (as1' ; as2')) *)
      | ProcImp.AST.AnnotatedSequence (as1, ProcImp.AST.AnnotatedSequence (as1', as2')) ->
      let () = print_endline "hello i'm here" in
      (List.map
	 (fun gamma ->
	   (first_control_point_names_of_annotated_stmt as1,
	    gamma,
	    [gamma],
	    first_control_point_names_of_annotated_stmt as1'))
	 gamma_alphabet)
    (*      @ transitions_of_fun (fun_name, ProcImp.AST.AnnotatedSequence (as1', as2')) *)

    (** as1 ; as2 *)
    | ProcImp.AST.AnnotatedSequence (as1, as2) ->
      List.map
	(fun gamma ->
	  (first_control_point_names_of_annotated_stmt as1,
	   gamma,
	   [gamma],
	   first_control_point_names_of_annotated_stmt as2))
	gamma_alphabet

    (** while (e) do as1 *)
    | ProcImp.AST.AnnotatedWhile (cpn, e, as1) ->
      (List.map
	 (fun gamma ->
	   (cpn,
	    gamma,
	    [gamma],
	    first_control_point_names_of_annotated_stmt as1))
	 gamma_alphabet)
      @ (List.map
	 (fun gamma ->
	   (last_control_point_names_of_annotated_stmt as1,
	    gamma,
	    [gamma],
	    cpn))
	 gamma_alphabet)
      @ transitions_of_fun (fun_name, as1)
    | ProcImp.AST.AnnotatedIfThenElse (cpn, e, as1, as2) ->
      (List.map
	 (fun gamma ->
	   (cpn,
	    gamma,
	    [gamma],
	    first_control_point_names_of_annotated_stmt as1))
	 gamma_alphabet)
      @ (List.map
	 (fun gamma ->
	   (cpn,
	    gamma,
	    [gamma],
	    first_control_point_names_of_annotated_stmt as2))
	 gamma_alphabet)
      @ transitions_of_fun (fun_name, as1)
      @ transitions_of_fun (fun_name, as2)
    (* faire avec l'appel de fonctions qui ne va pas plus loin *)
    | _ -> []
  in
  let transitions_pass_1 = List.flatten (List.map (transitions_of_fun) l) in
  transitions_pass_1
;;

let used_variables_of_expr e = 
  let rec aux_search_expr = function
    | ProcImp.AST.Plus   (e1, e2)           -> (aux_search_expr e1) @ (aux_search_expr e2) 
    | ProcImp.AST.Minus	 (e1, e2)           -> (aux_search_expr e1) @ (aux_search_expr e2) 
    | ProcImp.AST.Times	 (e1, e2)           -> (aux_search_expr e1) @ (aux_search_expr e2) 
    | ProcImp.AST.Integer  (n)	            -> []
    | ProcImp.AST.VariableEval (identifier) -> [identifier]
  in aux_search_expr e
;;

let used_constants_of_expr e =
  let rec aux_search_expr = function
    | ProcImp.AST.Plus    (e1, e2)     -> (aux_search_expr e1) @ (aux_search_expr e2) 
    | ProcImp.AST.Minus	  (e1, e2)     -> (aux_search_expr e1) @ (aux_search_expr e2) 
    | ProcImp.AST.Times	  (e1, e2)     -> (aux_search_expr e1) @ (aux_search_expr e2) 
    | ProcImp.AST.Integer (n)          -> [n]
    | ProcImp.AST.VariableEval (_)     -> []
  in aux_search_expr e
;;

let rec unannotate_stmt = function
  | ProcImp.AST.AnnotatedSkip         (cp)                    -> ProcImp.AST.Skip
  | ProcImp.AST.AnnotatedHalt	      (cp)                    -> ProcImp.AST.Halt
  | ProcImp.AST.AnnotatedSequence     (as1, as2)	      -> ProcImp.AST.Sequence (unannotate_stmt as1, unannotate_stmt as2)
  | ProcImp.AST.AnnotatedAssignment   (cp, x_name, e)	      -> ProcImp.AST.Assignment (x_name, e)
  | ProcImp.AST.AnnotatedFunCallStmt  (cp, f_name, expr_list) -> ProcImp.AST.FunCallStmt (f_name, expr_list)
  | ProcImp.AST.AnnotatedIfThenElse   (cp, e, as1, as2)	      -> ProcImp.AST.IfThenElse (e, unannotate_stmt as1, unannotate_stmt as2)
  | ProcImp.AST.AnnotatedWhile	      (cp, e, as')            -> ProcImp.AST.While (e, unannotate_stmt as')
  | ProcImp.AST.AnnotatedReturn	      (cp, e)                 -> ProcImp.AST.Return (e)
;;



let pds_cfg_of_program
    (p : ProcImp.AST.t)
    : ('a, 'b, 'c) PDS.t
    =
  let gamma_alphabet    = stack_alphabet_of_procimp_program p in
  let annotated_program = annotated_ast_of_program p in
  let unfactored_lambda = ref [] in
  let transitions = transitions_of_annotated_functions annotated_program gamma_alphabet in
  let nodes =
    let rec aux_get_nodes stmt =
      let unnotated_stmt = unannotate_stmt stmt in
      match stmt with
      | ProcImp.AST.AnnotatedSkip	 (cp)		   ->
	let () = unfactored_lambda := (cp, ProcImp.Is_stmt (unnotated_stmt)) :: !unfactored_lambda in
	[cp]
      | ProcImp.AST.AnnotatedHalt	 (cp)		   ->
	let () = unfactored_lambda := (cp, ProcImp.Is_stmt (unnotated_stmt)) :: !unfactored_lambda in
	[cp]
      | ProcImp.AST.AnnotatedSequence    (as1, as2)        ->
	(aux_get_nodes as1) @ (aux_get_nodes as2)
      | ProcImp.AST.AnnotatedAssignment  (cp, x_def, e)        ->
	let () = unfactored_lambda := (cp, ProcImp.Has_expr (e)) :: !unfactored_lambda in
	let () = unfactored_lambda := (cp, ProcImp.Is_stmt (unnotated_stmt)) :: !unfactored_lambda in
	let () = List.fold_left
	  (fun _ v -> unfactored_lambda := (cp, ProcImp.Use (v)) :: !unfactored_lambda)
	  ()
	  (used_variables_of_expr e) in
	let () = List.fold_left
	  (fun _ c -> unfactored_lambda := (cp, ProcImp.Conlit (c)) :: !unfactored_lambda)
	  ()
	  (used_constants_of_expr e) in
	let () = unfactored_lambda := (cp, ProcImp.Def (x_def)) :: !unfactored_lambda in
	[cp]
      | ProcImp.AST.AnnotatedFunCallStmt (cp, _, expr_list)        ->
	let () = List.fold_left
	  (fun _ e -> unfactored_lambda := (cp, ProcImp.Has_expr (e)) :: !unfactored_lambda)
	  ()
	  expr_list in
	let () = unfactored_lambda := (cp, ProcImp.Is_stmt (unnotated_stmt)) :: !unfactored_lambda in
	let () = List.fold_left
	  (fun _ e -> List.fold_left (fun _ v -> unfactored_lambda := (cp, ProcImp.Use (v)) :: !unfactored_lambda) () (used_variables_of_expr e))
	  ()
	  expr_list in
	let () = List.fold_left
	  (fun _ e -> List.fold_left (fun _ c -> unfactored_lambda := (cp, ProcImp.Conlit (c)) :: !unfactored_lambda) () (used_constants_of_expr e))
	  ()
	  expr_list in
	[cp]
      | ProcImp.AST.AnnotatedIfThenElse  (cp, _, as1, as2) -> cp :: (aux_get_nodes as1) @ (aux_get_nodes as2)
      | ProcImp.AST.AnnotatedWhile	 (cp, _, ast)	   -> cp :: (aux_get_nodes ast)
      | ProcImp.AST.AnnotatedReturn	 (cp, e)	   ->
	let () = unfactored_lambda := (cp, ProcImp.Has_expr (e)) :: !unfactored_lambda in
	let () = unfactored_lambda := (cp, ProcImp.Is_stmt (unnotated_stmt)) :: !unfactored_lambda in
	let () = List.fold_left
	  (fun _ v -> unfactored_lambda := (cp, ProcImp.Use (v)) :: !unfactored_lambda)
	  ()
	  (used_variables_of_expr e) in
	let () = List.fold_left
	  (fun _ c -> unfactored_lambda := (cp, ProcImp.Conlit (c)) :: !unfactored_lambda)
	  ()
	  (used_constants_of_expr e) in

	[cp]
    in ListMore.uniq (List.flatten (List.map (fun (_, annotated_s) -> aux_get_nodes annotated_s) annotated_program))
  in (nodes, transitions, [("main", 1)], ListMore.factor_merge_assoc !unfactored_lambda)
;;




type 'c product_states =
  | ProductJunkState     of ('c product_states * int)
  | ProductConcreteState of ('c)
;;

let rec max_junkstate_id = function
  | []                            -> 0
  | ProductConcreteState _  :: l' -> max_junkstate_id l'
  | ProductJunkState (_, n) :: l' -> max n (max_junkstate_id l')
;;

(**
   Returns the product APDS between PDS model [model] and SCTPLB formula [formula]. Considers [gamma_alphabet] as the set of a stack symbols of Γ.
*)
let model_formula_product_apds
    (model : ('a, 'b, 'c) PDS.t)
    (formula : 'b SCTPLB.t)
    (gamma_alphabet : ('a) list)
    =
  let (states_model, delta_model, initials_model, lambda_model) = model in
  let product_states =
    List.map (fun product_cp -> ProductConcreteState product_cp) (ListMore.cartesian_product states_model (SCTPLB.subformulas formula)) in
  let bigstar_states = ref [] in
  let product_delta : ('a, ('c * 'b SCTPLB.t) product_states) APDS.transition list ref = ref [] in
  let () =
    List.fold_left
      (fun _ gamma -> List.fold_left
	 (fun _ (ProductConcreteState (s, phi)) ->
	   let possible_transitions_with_s_gamma =
	     List.filter
	       (fun (s', gamma', _, _) -> s = s' && gamma = gamma')
	       delta_model
	   and possible_transitions_with_incoming_s_gamma =
	     List.filter
	       (fun (_, gamma', _, out_s') -> s = out_s' && gamma = gamma')
	       delta_model in
	   match phi with
	   | Atomic _         ->
	     ()
	   | Or (phi1, phi2)  ->
	     let () = product_delta := (ProductConcreteState (s, phi), gamma, [([gamma], ProductConcreteState (s, phi1))]) :: !product_delta in
	     let () = product_delta := (ProductConcreteState (s, phi), gamma, [([gamma], ProductConcreteState (s, phi2))]) :: !product_delta in
	     ()
	   | And (phi1, phi2) ->
	     let () = product_delta := (ProductConcreteState (s, phi), gamma, [([gamma], ProductConcreteState (s, phi1)) ; ([gamma], ProductConcreteState (s, phi2))]) :: !product_delta in
	     ()
	   | EX (phi')        ->
	     let () = List.fold_left
	       (fun _ (_, _, word, out_state) ->
		 let () = product_delta := (ProductConcreteState (s, phi), gamma, [(word, ProductConcreteState (out_state, phi'))]) :: !product_delta in
		 ()
	       )
	       ()
	       possible_transitions_with_s_gamma in 
	     ()
	   | AX (phi')        ->
	     let transitions_to_add =
	       List.map
		 (fun (_, _, w, out_state) ->
		   (w, ProductConcreteState (out_state, phi')))
		 possible_transitions_with_s_gamma in
	     let () = product_delta := (ProductConcreteState (s, phi), gamma, transitions_to_add) :: !product_delta in
	     ()
	   | EU (phi1, phi2)  ->
	     let () = product_delta := (ProductConcreteState (s, phi), gamma, [([gamma], ProductConcreteState (s, phi2))]) :: !product_delta in
	     let () = List.fold_left
	       (fun _ (_, _, word, out_state) ->
		 let () = product_delta :=
		   (ProductConcreteState (s, phi), gamma, [([gamma], ProductConcreteState (s, phi1)) ; (word, ProductConcreteState (out_state, phi))])
		   :: !product_delta in
		 ()
	       )
	       ()
	       possible_transitions_with_s_gamma in 
	     ()
	   | AU (phi1, phi2)  ->
	     let () = product_delta := (ProductConcreteState (s, phi), gamma, [([gamma], ProductConcreteState (s, phi2))]) :: !product_delta in
	     let transitions_to_add_snd_alt_trans =
	       ([gamma], ProductConcreteState (s, phi1)) :: List.map
		 (fun (_, _, w, out_state) ->
		   (w, ProductConcreteState (out_state, phi)))
		 possible_transitions_with_s_gamma in
	     let () = product_delta := (ProductConcreteState (s, phi), gamma, transitions_to_add_snd_alt_trans) :: !product_delta in
	     ()	     
	   | EXB (phi')       ->
	     let () = List.fold_left
	       (fun _ (inverse_state, _, word, _) -> match word with
		 | []           ->
		   List.fold_left
		     (fun _ gamma' ->
		       let () = product_delta :=
			 (ProductConcreteState (s, phi), gamma', [([gamma ; gamma'], ProductConcreteState (inverse_state, phi'))])
			 :: !product_delta in
		       ()
		     )
		     ()
		     gamma_alphabet
		 | _            ->
		   (let rec aux_make_stars current_product_state = function
		     | []           -> failwith "Unreachable case"
		     | [symb]       ->
		       let () = product_delta := (current_product_state, symb, [([gamma], ProductConcreteState (inverse_state, phi'))]) :: !product_delta in
		       ()
		     | symb :: word' ->
		       let new_star = match current_product_state with
			 | ProductConcreteState _               -> ProductJunkState (current_product_state, (max_junkstate_id !bigstar_states) + 1)
			 | ProductJunkState (product_state', n) -> ProductJunkState (product_state', n + 1) in
		       let () = bigstar_states := new_star :: !bigstar_states in
		       let () = product_delta :=
			 (current_product_state, symb, [([], new_star)])
			 :: !product_delta in
		       let () = aux_make_stars new_star word' in
		       ()
		    in aux_make_stars (ProductConcreteState (s, phi)) word
		   )
	       )
	       ()
	       possible_transitions_with_incoming_s_gamma in 
	     ()
	   | EUB (phi1, phi2)     ->
	     let () = List.fold_left
	       (fun _ (inverse_state, _, word, _) -> match word with
		 | [] ->
		   let () = product_delta := (ProductConcreteState (s, phi), gamma, [([gamma], ProductConcreteState (s, phi2))]) :: !product_delta in
		   List.fold_left
		     (fun _ gamma' ->
		       product_delta := (ProductConcreteState (s, phi), gamma', [([gamma'], ProductConcreteState (s, phi1)) ; ([gamma ; gamma'], ProductConcreteState (inverse_state, phi))]) :: !product_delta
		     )
		     ()
		     gamma_alphabet
		 | [w1] ->
		   let () = product_delta := (ProductConcreteState (s, phi), gamma, [([gamma], ProductConcreteState (s, phi2))]) :: !product_delta in
		   let () = product_delta := (ProductConcreteState (s, phi), w1, [([w1], ProductConcreteState (s, phi1)) ; ([gamma], ProductConcreteState (inverse_state, phi))]) :: !product_delta in
		   ()
		 | w1 :: word' ->
		   let () = product_delta := (ProductConcreteState (s, phi), gamma, [([gamma], ProductConcreteState (s, phi2))]) :: !product_delta in
		   let bigstar1 = ProductJunkState (ProductConcreteState (s, phi), (max_junkstate_id !bigstar_states) + 1) in
		   let () = bigstar_states := bigstar1 :: !bigstar_states in
		   let () = product_delta := (ProductConcreteState (s, phi), w1, [([w1], ProductConcreteState (s, phi1)) ; ([], bigstar1)]) :: !product_delta in
		      (let rec aux_make_stars current_product_state = function
			| []           -> failwith "Unreachable case"
			| [symb]       ->
			  let () = product_delta := (current_product_state, symb, [([gamma], ProductConcreteState (inverse_state, phi))]) :: !product_delta in
			  ()
			| symb :: word'' ->
			  let new_star = match current_product_state with
			    | ProductConcreteState _               -> ProductJunkState (current_product_state, (max_junkstate_id !bigstar_states) + 1)
			    | ProductJunkState (product_state', n) -> ProductJunkState (product_state', n + 1) in
			  let () = bigstar_states := new_star :: !bigstar_states in
			  let () = product_delta := (current_product_state, symb, [([], new_star)]) :: !product_delta in
			  let () = aux_make_stars new_star word'' in
			  ()
		       in aux_make_stars bigstar1 word'
		   )
	       )
	       ()
	       possible_transitions_with_incoming_s_gamma in
	     ()
  	   | _ -> failwith "Missing cases for transition generation in product APDS : TODO"
	 )
	 ()
	product_states)
      ()
      gamma_alphabet in
  let product_initials = List.map (fun product_cp -> ProductConcreteState product_cp) (ListMore.cartesian_product states_model [formula]) in
  let product_lambda = [] (* BUG: idem *) in
  (product_states @ !bigstar_states, !product_delta, product_initials, product_lambda)
;;

let c_true_ama_set_of_pds
    (model : ('a, 'b, 'c) PDS.t)
    (gamma_alphabet : ('a) list)
    : ('a, ('c * 'b SCTPLB.t)) AMA.t
    =
  let (states_model, delta_model, initials_model, lambda_model) = model in
  let c_true_ama_states =
    let rec aux_loop lambda = match lambda with
    | []                       -> []
    | (cp, atomics) :: lambda' ->
      (List.map (fun atom_term -> (cp, SCTPLB.Atomic (atom_term))) atomics)
      @ (aux_loop lambda')
    in aux_loop lambda_model in
  let c_true_ama_delta = List.flatten (List.map
    (fun (cp, atomic_phi) -> List.map
      (fun gamma -> ((cp, atomic_phi), gamma, [(cp, atomic_phi)])) gamma_alphabet)
    c_true_ama_states) in
  (* BUG : need to be sure : what is an initial state in model-checking ? *)
  let c_true_ama_initials =
    List.filter
      (fun (cp, _) -> List.exists (fun x -> x = cp) initials_model)
      c_true_ama_states in
  let c_true_ama_finals =
    c_true_ama_states
  in (c_true_ama_states, c_true_ama_delta, c_true_ama_initials, c_true_ama_finals)
;;

let product_states_injection
    ama
    (* (ama  : ('a, 'c product_states) t) *)
    (*    : ('a, 'c product_states) t    *)
    =
  let (states, delta, initials, finals) = ama in
  let pre_states = List.map (fun (s, phi) -> ProductConcreteState (s, phi)) states in
  let pre_delta = List.map (fun (cp, gamma, cp_list) -> (ProductConcreteState cp, gamma, List.map (fun (s, phi) -> ProductConcreteState (s, phi)) cp_list)) delta in
  let pre_initials = List.map (fun (s, phi) -> ProductConcreteState (s, phi)) initials in
  let pre_finals = List.map (fun (s, phi) -> ProductConcreteState (s, phi)) finals in
  (pre_states, pre_delta, pre_initials, pre_finals)
;;

(*
let t0 : (ProcImp.AST.identifier, (string * int)) PDS.transition list = transitions_of_annotated_functions annot_ast0;;
let init0 : (string * int) PDS.control_point list = [("main", 1)];;

let pds_pre_0 : ('a, 'b, 'c) PDS.t = (
  [1 ; 2],
  [(1, 'f', [], 1) ;
   (2, 'e', ['d'], 2) ;
   (1, 'e', ['e' ; 'c'], 2) ;
  ],
  [1],
  [
    (1, [1 ; 3]) ;
    (2, [1 ; 2])
  ]
);;

let phi_0 = SCTPLB.EX (SCTPLB.And (SCTPLB.Atomic (2), SCTPLB.AX (SCTPLB.Atomic (1))));;

let phi_1 = SCTPLB.And (SCTPLB.Or (SCTPLB.Atomic 1, SCTPLB.Atomic 2), SCTPLB.Atomic 3);;

let apds_prod_0 = model_formula_product_apds 
  pds_pre_0
  phi_0
  [ 'a' ; 'b' ; 'c' ; 'd' ; 'e' ; 'f' ]
;;


let pre_star_ama_0 = AMA.ama_of_pre_star apds_prod_0 (AMA.pre_states_injection (product_states_injection c_true_ama_0));;
*)


(*
  BUG pour (ConcreteState (2, phi_0), ['e' ; 'd'])
*)




(*
let annotated_p0 = annotated_ast_of_program p0;;
let trans0 = transitions_of_annotated_functions annotated_p0 stack_alpha0;;
*)


(**
   Decides wheter ProcImp program [program] at initial control point satisfies SCTPLB formula [formula] with stack word [stack_word]
*)
let program_model_checking_at_default_initial_control_point
    (program : ProcImp.AST.t)
    (formula : 'b SCTPLB.t)
    stack_word
    =
  let intial_program_control_point = ("main", 1) in
  let program_model  = pds_cfg_of_program program in
  let stack_alphabet = stack_alphabet_of_procimp_program program in
  let initial_true_configurations = c_true_ama_set_of_pds program_model stack_alphabet in
  let apds_product_model_formula = model_formula_product_apds program_model formula stack_alphabet in
  let pre_star_ama_of_apds_product = AMA.ama_of_pre_star apds_product_model_formula (AMA.pre_states_injection (product_states_injection initial_true_configurations)) in
  let result = AMA.execute
    pre_star_ama_of_apds_product
    (ConcreteState (ProductConcreteState (intial_program_control_point, formula)), stack_word) in
  result
;;



(**
   Returns control points in which ProcImp program [program] satisfies SCTPLB formula [formula]
*)
let program_model_checking
    (program : ProcImp.AST.t)
    (formula : 'b SCTPLB.t)
    intial_program_control_point
    stack_word
    =
  let program_model  = pds_cfg_of_program program in
  let stack_alphabet = stack_alphabet_of_procimp_program program in
  let initial_true_configurations = c_true_ama_set_of_pds program_model stack_alphabet in
  let apds_product_model_formula = model_formula_product_apds program_model formula stack_alphabet in
  let pre_star_ama_of_apds_product = AMA.ama_of_pre_star apds_product_model_formula (AMA.pre_states_injection (product_states_injection initial_true_configurations)) in
  let result = AMA.execute
    pre_star_ama_of_apds_product
    (ConcreteState (ProductConcreteState (intial_program_control_point, formula)), stack_word) in
  result
;;

(**
   Returns control points in which ProcImp program [program] satisfies SCTPLB formula [formula]
*)
let pds_model_checking
    pds
    (formula : 'b SCTPLB.t)
    intial_program_control_point
    stack_word
    stack_alphabet
    =
  let initial_true_configurations = c_true_ama_set_of_pds pds stack_alphabet in
  let apds_pds_formula = model_formula_product_apds pds formula stack_alphabet in
  let pre_star_ama_of_apds_product = AMA.ama_of_pre_star apds_pds_formula (AMA.pre_states_injection (product_states_injection initial_true_configurations)) in
  let result = AMA.execute
    pre_star_ama_of_apds_product
    (ConcreteState (ProductConcreteState (intial_program_control_point, formula)), stack_word) in
  result
;;


(* LOOPS *)
(*
let program_model_checking
    (program : ProcImp.AST.t)
    (formula : 'b SCTPLB.t)
    =
  let program_model  = pds_cfg_of_program program in
  let stack_alphabet = stack_alphabet_of_procimp_program program in
  let initial_true_configurations = c_true_ama_set_of_pds program_model stack_alphabet in
  let apds_product_model_formula = model_formula_product_apds program_model formula stack_alphabet in
  let pre_star_ama_of_apds_product = AMA.ama_of_pre_star apds_product_model_formula (AMA.pre_states_injection (product_states_injection initial_true_configurations)) in

  let (_, _, initials_of_product_apds, _) = apds_product_model_formula in
  
  List.filter (fun state -> AMA.liberal_execute pre_star_ama_of_apds_product (ConcreteState state)) initials_of_product_apds
;;
*)

(*
let pds_0 : ('a, 'b, 'c) PDS.t = (
  [1 ; 2],
  [(1, 'f', [], 1) ;
   (2, 'e', ['d'], 2) ;
   (1, 'e', ['d' ; 'c'], 2) ;
  ],
  [1],
  [
    (1, [1 ; 3]) ;
    (2, [1 ; 2])
  ]
);;


let phi_0 = SCTPLB.EU (SCTPLB.Atomic (1), SCTPLB.Atomic (2));;


let apds_prod_0 = model_formula_product_apds 
  pds_0
  phi_0
  [ 'c' ; 'd' ; 'e' ; 'f' ]
;;


let c_true_ama_0 = c_true_ama_set_of_pds pds_0 [ 'c' ; 'd' ; 'e' ; 'f' ];;

let pre_star_ama_0 = AMA.ama_of_pre_star apds_prod_0 (AMA.pre_states_injection (product_states_injection c_true_ama_0));;


let (_, x0, _, _) = pre_star_ama_0;;


List.length x0;;
List.nth x0 25;;

AMA.execute
  (AMA.ama_of_pre_star apds_prod_0 (AMA.pre_states_injection (product_states_injection c_true_ama_0)))
  (ConcreteState (ProductConcreteState (2, phi_0)), []);;
*)
