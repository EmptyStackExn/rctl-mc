(*
#load "Fixpoint.cmo"
#load "Prop.cmo";;
#load "ListMore.cmo"
#load "APDS.cmo"
*)
open Fixpoint;;
open Prop;;
open ListMore;;
open APDS;;

type 'a alphabet_symbol  = ('a)
type 'a alphabet_word    = ('a alphabet_symbol) list
type 'c control_point    = ('c)
type ('a, 'c) transition =
      ('c control_point)
    * ('a alphabet_symbol)
    * ('c control_point list)

(**
   Main of type of AMA
*)
type ('a, 'c) t =
      'c control_point list    (* liste des points de contrôles de l'AMA *) 	
    * ('a, 'c) transition list (* liste des transitions *)
    * 'c control_point list    (* liste des initiaux *)
    * 'c control_point list    (* liste des finaux *)

(**
   Type of configurations during execution of AMA on words
*)
type ('a, 'c) configuration = ('c control_point) * ('a alphabet_word)

let matches_first_symbol_with_word (s : 'a alphabet_symbol) (w : 'a  alphabet_word) = match w with
  | []       -> false (* failwith "TODO AMA 1st symbol of word cmp" *)
  | s' :: w' -> s' = s
;;

let consume_letter_of_word (w : 'a alphabet_word) = match w with
  | []      -> [] (* failwith "TODO AMA 2nds failwith" *)
  | _ :: w' -> w'
;;

(**
   In the AMA [(control_points, delta, initials, finals)], returns the superset of succesor of configurations of [l]
*)
let next_of_states
    ((control_points, delta, initials, finals) : ('a, 'c) t)
    (l : ('a, 'c) configuration list list)
    =
  let dnf_formula = Prop.formula_of_dnf_clause_system l in
  let propagate_next_of_conf_literal (phi : (('a, 'c) configuration) Prop.formula) =
    match phi with
      | Literal (cp0, word0) ->
    let possible_transitions =
    List.filter
      (fun (cp, gamma, out_trans) ->
	cp = cp0
	&& matches_first_symbol_with_word gamma word0)
      delta in
    let next_conf =
      List.map (fun (cp, gamma, out_trans) ->
	List.map (fun cp_next ->
	  (cp_next, consume_letter_of_word word0)) out_trans) possible_transitions in
    (match next_conf with
      | [] -> Literal (cp0, word0) (* FEINTE ! triche parce qu'on a autopate de Büchi !!!! *)
      | _  -> Prop.formula_of_dnf_clause_system next_conf)
      | _ -> failwith "Not supposed to have else that literals" in
  let rec substitute_one_step f = match f with
    | Literal x    -> propagate_next_of_conf_literal (Literal x)
    | And (f1, f2) -> And (substitute_one_step f1, substitute_one_step f2)
    | Or (f1, f2)  -> Or (substitute_one_step f1, substitute_one_step f2)
    | Not (f')     -> failwith "Not operator, not to be managed" in
  let propagated_formula = substitute_one_step dnf_formula in
  let dirty_dnf_clause_system = Prop.dnf_clause_system_of_formula propagated_formula in
  ListMore.double_uniq dirty_dnf_clause_system
;;

(**
   In the AMA [(control_points, delta, initials, finals)], returns the superset of succesor of states [l], unregarding edge labels
*)
let liberal_next_of_states
    ((control_points, delta, initials, finals) : ('a, 'c) t)
    (l : 'c control_point list list)
    =
  let dnf_formula = Prop.formula_of_dnf_clause_system l in
  let propagate_next_of_conf_literal (s : ('c control_point) Prop.formula) =
    match s with
      | Literal (cp0) ->
    let possible_transitions =
    List.filter
      (fun (cp, _, _) ->
	cp = cp0)
      delta in
    let next_conf =
      List.map (fun (cp, gamma, out_trans) ->
	List.map (fun cp_next ->
	  cp_next) out_trans) possible_transitions in
    (match next_conf with
      | [] -> Literal (cp0) (* FEINTE ! triche parce qu'on a autopate de Büchi !!!! *)
      | _  -> Prop.formula_of_dnf_clause_system next_conf)
      | _ -> failwith "Not supposed to have else that literals" in
  let rec substitute_one_step f = match f with
    | Literal x    -> propagate_next_of_conf_literal (Literal x)
    | And (f1, f2) -> And (substitute_one_step f1, substitute_one_step f2)
    | Or (f1, f2)  -> Or (substitute_one_step f1, substitute_one_step f2)
    | Not (f')     -> failwith "Not operator, not to be managed" in
  let propagated_formula = substitute_one_step dnf_formula in
  let dirty_dnf_clause_system = Prop.dnf_clause_system_of_formula propagated_formula in
  ListMore.double_uniq dirty_dnf_clause_system
;;


(**
   Execution of the AMA [ama] on word [m]
*)
let execute
    (ama : ('a, 'c) t)
    (m : ('a, 'c) configuration) =
  let fix_p = Fixpoint.fp (next_of_states ama) [[m]] in
  let (_, _, _, finals) = ama in
  List.exists (fun l -> List.for_all (fun (cp, _) -> List.exists (fun x -> x = cp) finals) l) fix_p
;;

(**
   Execution of the AMA [ama] on word [m]
*)
let liberal_execute
    (ama : ('a, 'c) t)
    (m : 'c control_point) =
  let fix_p = Fixpoint.fp (liberal_next_of_states ama) [[m]] in
  let (_, _, _, finals) = ama in
  List.exists (fun l -> List.for_all (fun cp -> List.exists (fun x -> x = cp) finals) l) fix_p
;;

(**
   Construction of pre*
*)

type 'c pre_states =
  (* ['c pre_states] parce qu'on veut garder l'information de l'état concret d'où l'on est venu, on veut donc spécifiquement du "ConcreteState" et *pas* autre chose *)
  | JunkState     of ('c pre_states) * int
  | ConcreteState of ('c)

(**
   Returns an AMA that recognizes L ([ama]) + { <[cp], [word]> }
*)
let add_recognition_of_word
    ((control_points, delta, initials, finals) : ('a, 'c) t)
    ((cp, word) : ('a, 'c) configuration)
    (* : ('a, 'c pre_states) t *)
    =
  let max_junk_state_id : int =
    List.fold_left
      (fun a b -> match b with
	| JunkState (_, n) -> max a n
	| _                -> failwith "Not supposed to get here!")
      0
      (List.filter
	 (function
	   | JunkState _ -> true
	   | _           -> false
	 )
	 control_points) in
  let counter = ref max_junk_state_id in
  let next_counter () = let () = counter := !counter + 1 in !counter in

  let control_points' =
    if (List.for_all (fun x -> x <> cp) control_points)
    then ref (cp :: control_points)
    else ref control_points in

  let finals' = ref finals in

  let delta'  = ref delta in

  let rec aux_on_word current_state w =
    let original_state : int pre_states control_point = match current_state with
      | ConcreteState x  -> ConcreteState x
      | JunkState (x, n) -> x in
    match w with
      | []         ->
	if (List.exists (fun x -> x = current_state) !finals')
	then ()
	else finals' := current_state :: !finals'
      | symb :: w' ->
	let possible_transitions =
	  List.filter
	    (fun (s0, gamma0, _) -> s0 = original_state && symb = gamma0)
	    !delta' in
	(match possible_transitions with
	  | []                     ->
	    let junk_state = JunkState (original_state, next_counter ()) in
	    let () = control_points' := junk_state :: !control_points' in
	    let () = delta' := (current_state, symb, [junk_state]) :: !delta' in
	    aux_on_word junk_state w'
	  | [(cp0, _, [])]         -> failwith "Transition without out states in AMA ?"
	  | [(cp0, _, [cp1])]      ->
	    aux_on_word cp1 w'
	  | _                      -> failwith "BUG, what to do in such case? several out states when adding recognition") in

  let () = aux_on_word cp word in
  (!control_points', !delta', initials, !finals')
;;

let ama_empty = ([], [], [], []);;

(**
   Returns an AMA that recognizes [c_true]
*)
let ama_of_configuration_list
    (c_true : ('a, 'c) configuration list)
    =
  List.fold_left
    (fun ama (cp, word) -> add_recognition_of_word ama (ConcreteState cp, word))
    ama_empty
    c_true
;;

(** Example *)
let ama0 : ('a, 'c) t = (
  [1 ; 2 ; 3],
  [
    (1, 'a', [2 ; 3]) ;
    (2, 'a', [2]) ;
    (3, 'a', [1])
  ],
  [1],
  [1 ; 2]
);;
let c0 : ('a, 'c) configuration list list = [[(1, ['a' ; 'a'])]];;
let _ = execute ama0 (1, ['a' ; 'a']);;

(*
  Fixpoint.fp (next_of_states ama0) c0;;
  let u1 = (next_of_states ama0) c0;;
  let u1 = (next_of_states ama0) u1;;
*)


let cs0 : ('a, 'c) configuration list = [(2, ['a' ; 'b' ; 'c']) ; (2, ['a' ; 'b']) ; (3, ['b' ; 'a'])];;

let ama0 = ama_of_configuration_list cs0;;

next_of_states ama0 [[(ConcreteState 1, [])]];;

(*
let u0 : ('a, 'c) t = add_recognition_of_word ama_empty (ConcreteState 1, ['a' ; 'b']);;
print_endline ("");;
let u1 : ('a, 'c) t = add_recognition_of_word u0 (ConcreteState 2, ['a']);;
*)

execute ama0 (ConcreteState 3, ['b' ; 'a' ; 'c']);;

(** Pre* example *)

let apds_pre_0 : ('a, 'b, 'c) APDS.t = (
  [1 ; 2],
  [(1, 'f', [([], 1)]) ;
   (2, 'd', [(['a' ; 'b'], 2)]) ;
   (1, 'e', [(['d' ; 'c'], 2)]) ;
  ],
  [1],
  []
);;

let ama_pre_0 = ama_of_configuration_list [(2, ['a' ; 'b' ; 'c'])];;

(* notations wrt Bouajjani's paper *)
(* BUG dans l'union des P1
let pre_star_functional
    (apds : ('a, 'b, 'c) APDS.t)
    (ama  : ('a, 'c pre_states) t)
    =
  let (control_points_apds, delta_apds, initials_apds, lambda_apds) = apds
  and (control_points_ama, delta_ama, initials_ama, finals_ama)     = ama in
  let new_transitions = ref [] in
  let () =
    List.fold_left
      (fun _ (cp_j, gamma, cp_l_k_w) ->
	List.fold_left
	  (fun _ (w_k, p_k) ->
	    let () =
	      let fix_p = Fixpoint.fp (next_of_states ama) [[(ConcreteState p_k, w_k)]] in
	      let merde = List.filter (fun conj_l -> not (List.exists (fun (_, l) -> l <> []) conj_l)) fix_p in
	      let merde2 = List.map (fun (pre_state, _) -> pre_state) (List.flatten merde) in
	      new_transitions :=
		(cp_j,
		 gamma,
		 merde2)
	      :: !new_transitions in ())
	  ()
	  cp_l_k_w)
      ()
      delta_apds in
  let propagation = List.filter (fun (_, _, l) -> l <> []) !new_transitions in
  let s_j_of_p_j = List.map (fun (state, x, y) -> (ConcreteState state, x, y)) propagation in
  (control_points_ama, ListMore.uniq (delta_ama @ s_j_of_p_j), initials_ama, finals_ama)
;;
*)

let pre_star_functional
    (apds : ('a, 'b, 'c) APDS.t)
    (ama  : ('a, 'c pre_states) t)
    =
  let (control_points_apds, delta_apds, initials_apds, lambda_apds) = apds
  and (control_points_ama, delta_ama, initials_ama, finals_ama)     = ama in
  let new_transitions = ref [] in
  let () =
    List.fold_left
      (fun _ (cp_j, gamma, cp_l_k_w) ->
	let p_set = List.flatten (List.map
	  (fun (w_k, p_k) ->
	    let fix_p = Fixpoint.fp (next_of_states ama) [[(ConcreteState p_k, w_k)]] in
	    let merde = List.filter (fun conj_l -> not (List.exists (fun (_, l) -> l <> []) conj_l)) fix_p in
	    let merde2 = List.map (fun (pre_state, _) -> pre_state) (List.flatten merde)
	    in merde2)
	  cp_l_k_w) in
	new_transitions := (cp_j, gamma, p_set) :: !new_transitions
      )
      ()
      delta_apds in
  let propagation = List.filter (fun (_, _, l) -> l <> []) !new_transitions in
  let s_j_of_p_j = List.map (fun (state, x, y) -> (ConcreteState state, x, y)) propagation in
  let uniq_forall_transition = List.map (fun (x1, x2, l) -> (x1, x2, ListMore.uniq l)) (delta_ama @ s_j_of_p_j) in
  (control_points_ama, ListMore.uniq uniq_forall_transition, initials_ama, finals_ama)
;;


let ama_pre_1 = pre_star_functional apds_pre_0 ama_pre_0;;
let ama_pre_2 = pre_star_functional apds_pre_0 ama_pre_1;;
let ama_pre_2 = pre_star_functional apds_pre_0 ama_pre_2;;


Fixpoint.fp (next_of_states ama_pre_0) [[(ConcreteState 2, ['a' ; 'b'])]];;

(* Avant rajout d'un type particulier pour les états différenciés des poubelles dans l'APDS produit entre modèle et formule *)

let pre_states_injection
    (ama  : ('a, 'c) t)
    : ('a, 'c pre_states) t
    =
  let (states, delta, initials, finals) = ama in
  let pre_states = List.map (fun s -> ConcreteState s) states in
  let pre_delta = List.map (fun (cp, gamma, cp_list) -> (ConcreteState cp, gamma, List.map (fun s -> ConcreteState s) cp_list)) delta in
  let pre_initials = List.map (fun s -> ConcreteState s) initials in
  let pre_finals = List.map (fun s -> ConcreteState s) finals in
  (pre_states, pre_delta, pre_initials, pre_finals)
;;


(**
   Returns an AMA that recognizes the set pre* (C_true) in the APDS [apds] when C_true is recognized by AMA [ama]
*)
let ama_of_pre_star
    (apds : ('a, 'b, 'c) APDS.t)
    (ama  : ('a, 'c pre_states) t)
    =
Fixpoint.fp (pre_star_functional apds) ama;;

ama_of_pre_star apds_pre_0 ama_pre_0;;

(**
   Emptiness problem of AMA
*)

(* let denotes_empty_of_ama
    (ama : ('a, 'c) t)
    =
  let (ama_states, ama_delta, ama_initials, ama_finals) = ama in
  let is_final s = List.exists (fun s' -> s = s') ama_finals in
  List.exists
    (fun cp_i ->
      let rec aux_parcours s = 
	let next = List.filter (fun (cp, gamma, cp_list) -> cp_i = cp) ama_delta in
	if next = []
	then is_final s
	else List.exists (fun (_, _, cp_list) -> List.for_all (fun cp -> aux_parcours cp) cp_list) next
      in aux_parcours cp_i
    )
    ama_initials
;;
*)

(** Pre* example *)



let apds_pre_0 : ('a, 'b, 'c) APDS.t = (
  [1 ; 2],
  [(1, 'a', [([], 1) ; (['b'], 2)]) ;
  ],
  [1],
  []
);;

let ama_pre_0 = pre_states_injection (
  [1 ; 2],
  [
    (2, 'a', [2]) ;
    (2, 'b', [2]) ;
  ],
  [],
  []
);;
(*
let ama_pre_1 = pre_star_functional apds_pre_0 ama_pre_1;;

Fixpoint.fp (next_of_states ama_pre_1) [[(ConcreteState 2, [])]];;

(* (wk, pk) = ([], 1) *)
let fix_p = Fixpoint.fp (next_of_states ama_pre_0) [[(ConcreteState 1, [])]];;
let merde = List.filter (fun conj_l -> not (List.exists (fun (_, l) -> l <> []) conj_l)) fix_p;;


let new_transitions = ref [];;
let merde2 = List.map (fun (pre_state, _) -> pre_state) (List.flatten merde) ;;


let pre_star_functional
    (apds : ('a, 'b, 'c) APDS.t)
    (ama  : ('a, 'c pre_states) t)
    =
  let (control_points_apds, delta_apds, initials_apds, lambda_apds) = apds
  and (control_points_ama, delta_ama, initials_ama, finals_ama)     = ama in
  let new_transitions = ref [] in
  let () =
    List.fold_left
      (fun _ (cp_j, gamma, cp_l_k_w) ->
	let p_set = List.flatten (List.map
	  (fun (w_k, p_k) ->
	    let fix_p = Fixpoint.fp (next_of_states ama) [[(ConcreteState p_k, w_k)]] in
	    let merde = List.filter (fun conj_l -> not (List.exists (fun (_, l) -> l <> []) conj_l)) fix_p in
	    let merde2 = List.map (fun (pre_state, _) -> pre_state) (List.flatten merde)
	    in merde2)
	  cp_l_k_w) in
	new_transitions := (cp_j, gamma, p_set) :: !new_transitions
      )
      ()
      delta_apds in
  let propagation = List.filter (fun (_, _, l) -> l <> []) !new_transitions in
  let s_j_of_p_j = List.map (fun (state, x, y) -> (ConcreteState state, x, y)) propagation in
  let uniq_forall_transition = List.map (fun (x1, x2, l) -> (x1, x2, ListMore.uniq l)) (delta_ama @ s_j_of_p_j) in
  (control_points_ama, ListMore.uniq uniq_forall_transition, initials_ama, finals_ama)
;;


List.flatten (List.map
		(fun (w_k, p_k) ->
		  let fix_p = Fixpoint.fp (next_of_states ama_pre_0) [[(ConcreteState p_k, w_k)]] in
		  let merde = List.filter (fun conj_l -> not (List.exists (fun (_, l) -> l <> []) conj_l)) fix_p in
		  let merde2 = List.map (fun (pre_state, _) -> pre_state) (List.flatten merde)
		  in merde2)
		[([], 1) ; (['b'], 2)]);;

Fixpoint.fp (next_of_states ama_pre_0) [[(ConcreteState 2, ['b'])]]
*)
