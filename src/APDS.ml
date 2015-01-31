(*
  'a : type of symbols of stack
  'b : type of atomic predicates
  'c : type of control_points
*)
(* here for a program in ProcImp
   'a is ProcImp.AST.identifier
   'b is ProcImp.procimp_atomic_predicate
   'c is (string * int) * (ProcImp.procimp_atomic_predicate) SCTPLB.AST.t
*)

(*
#load "Fixpoint.cmo"
#load "Prop.cmo"
*)
open Fixpoint;;
open Prop;;

(* here it's ProcImp.AST.identifier *)
type 'a stack_symbol  = ('a)
type 'a stack_word    = 'a list
type 'c control_point = ('c)
type ('a, 'c) transition   = 'c control_point * 'a stack_symbol * ('a stack_word * 'c control_point) list

(* here it's ProcImp.AST.l0_atomic_predicate *)
type 'b atomic_predicate = ('b)

(**
   Main of type of APDS
*)
type ('a, 'b, 'c) t =
    'c control_point list                                      (* list of controls point of program *) 
    * (('a, 'c) transition list)			       (* transitions of the CFG *) 
    * 'c control_point list				       (* initial control points of program *) 
    * (('c control_point * (('b atomic_predicate) list)) list) (* association of a control point to a set of atomic predicates *)

type ('a, 'c) configuration = 'c control_point * 'a stack_word

let matches_top_stack_symbol (c : 'a stack_symbol) (w : 'a stack_word) : bool =
  List.nth w 0 = c
;;

(* retirer le premier symbole de w et foutre w' à la place *)
let stack_substitution (w : 'a stack_word) (w_next : 'a stack_word) = match w with
  | []       -> failwith "Empty stack. Can't continue PDS execution"
  | s' :: w' -> w_next @ w'
;;

(**
   In the APDS [(control_points, delta, initials, lambda)], returns the superset of succesor of configurations of [l]
*)
let next_of_conf
    ((control_points, delta, initials, lambda) : ('a, 'b, 'c) t)
    (l : ('a, 'c) configuration list list)
    =
  let dnf_formula = Prop.formula_of_dnf_clause_system l in
  let propagate_next_of_conf_literal = function
    | Literal (cp0, word0) -> 
      let possible_transitions =
	List.filter
	  (fun (cp, gamma, out_trans) -> cp = cp0 && matches_top_stack_symbol gamma word0)
	  delta in
      let next_conf = List.map (fun (cp, gamma, out_trans) -> List.map (fun (w', cp_next) -> (cp_next, stack_substitution word0 w')) out_trans) possible_transitions in
      (match next_conf with
      | [] -> Literal (cp0, word0) (* triche parce qu'on a autopate de Büchi !!!! *)
      | _  -> Prop.formula_of_dnf_clause_system next_conf )
    | _ -> failwith "Here's supposed to use only literals for propagation of states for alternating transitions"
in
  let rec substitute_one_step f = match f with
    | Literal x    -> propagate_next_of_conf_literal (Literal x)
    | And (f1, f2) -> And (substitute_one_step f1, substitute_one_step f2)
    | Or (f1, f2)  -> Or (substitute_one_step f1, substitute_one_step f2)
    | Not (f')     -> failwith "Not operator, not to be managed" in
  let propagated_formula = substitute_one_step dnf_formula in
  Prop.dnf_clause_system_of_formula propagated_formula
;;

(**
  In the APDS [apds], returns the reflexive-transitive closure of next of configuration [initial_conf]
*)
let stuck_states_of_execution
    apds
    initial_conf
    =
  Fixpoint.fp (next_of_conf apds) initial_conf
;;

(** DANGER DE MORT *)
(*
let execute
    (apds : ('a, 'b, 'c) t)
    (initial_conf : 'a stack_word)
    (is_a_final_state : ('a, 'c) configuration -> bool)
    =
  let stuck_states = stuck_states_of_execution apds initial_conf in
  List.exists (fun l -> List.for_all (is_a_final_state) l) stuck_states
;;
*)


(**
   Execution of the APDS [apds] with [initial_conf] as initial configuration considering that [is_a_final_conf] recognizes the set of final Büchi configurations
*)
let execute
    (apds : ('a, 'b, 'c) t)
    (initial_conf : ('a, 'c) configuration list list)
    (is_a_final_conf : ('a, 'c) configuration -> bool)
    =
  let stuck_states = stuck_states_of_execution apds initial_conf in
  List.exists (fun l -> List.for_all (is_a_final_conf) l) stuck_states
;;

(** examples *)
let apds0 : ('a, 'b, 'c) t = (
  [1 ; 2 ; 3 ; 4 ; 5 ; 6 ; 7],
  [(1, 'a', [([], 2) ; (['b'], 3)]) ;
   (2, 'b', [([], 4)]) ;
   (2, 'b', [(['b'], 5)]) ;
   (3, 'b', [(['c'], 6)]) ;
   (3, 'b', [(['b'], 7)]) ;

   (*
   (1, 'a', [(['a'], 1)]) ; (1, 'b', [(['b'], 1)]) ; (1, 'c', [(['c'], 1)]) ; (1, 'd', [(['d'], 1)]) ; 
   (2, 'a', [(['a'], 2)]) ; (2, 'b', [(['b'], 2)]) ; (2, 'c', [(['c'], 2)]) ; (2, 'd', [(['d'], 2)]) ; 
   (3, 'a', [(['a'], 3)]) ; (3, 'b', [(['b'], 3)]) ; (3, 'c', [(['c'], 3)]) ; (3, 'd', [(['d'], 3)]) ; 
   (4, 'a', [(['a'], 4)]) ; (4, 'b', [(['b'], 4)]) ; (4, 'c', [(['c'], 4)]) ; (4, 'd', [(['d'], 4)]) ; 
   (5, 'a', [(['a'], 5)]) ; (5, 'b', [(['b'], 5)]) ; (5, 'c', [(['c'], 5)]) ; (5, 'd', [(['d'], 5)]) ; 
   (6, 'a', [(['a'], 6)]) ; (6, 'b', [(['b'], 6)]) ; (6, 'c', [(['c'], 6)]) ; (6, 'd', [(['d'], 6)]) ; 
   (7, 'a', [(['a'], 7)]) ; (7, 'b', [(['b'], 7)]) ; (7, 'c', [(['c'], 7)]) ; (7, 'd', [(['d'], 7)]) ; 
   *)

  ],
  [1],
  []
);;

let c0 = (1, ['a' ; 'b' ; 'd' ; 'd' ; 'd']);;

stuck_states_of_execution apds0 [[c0]];;



execute
  apds0
  [[c0]]
  (function
    | (4, _) ->  true
    | (5, _) ->  true
    | (6, _) ->  true
    | (7, _) ->  true
    | _ -> false
)
;;



let u0 = next_of_conf apds0 [[c0]];;
let u0 = next_of_conf apds0 u0;;


(*
let u2 = next_of_conf apds0 u1;;

let y1 = Prop.formula_of_dnf_clause_system u1;;
let (control_points, delta, initials, lambda) = apds0;;

let propagate_next_of_conf_literal (Literal (cp0, word0)) =
    let possible_transitions =
    List.filter
      (fun (cp, gamma, out_trans) -> cp = cp0 && matches_top_stack_symbol gamma word0)
      delta in
    let next_conf =
      List.map (fun (cp, gamma, out_trans) -> List.map (fun (w', cp_next) -> (cp_next, stack_substitution word0 w')) out_trans) possible_transitions in
    match next_conf with
      | [] -> Literal (cp0, word0) (* triche *)
      | _  -> Prop.formula_of_dnf_clause_system next_conf
;;

let rec substitute_one_step f = match f with
    | Literal x    -> propagate_next_of_conf_literal (Literal x)
    | And (f1, f2) -> And (substitute_one_step f1, substitute_one_step f2)
    | Or (f1, f2)  -> Or (substitute_one_step f1, substitute_one_step f2)
    | Not (f')     -> failwith "Not operator, not to be managed"
;;



let propagated_formula = substitute_one_step y1;;

  propagate_next_of_conf_literal (Literal (6, ['c'; 'b'; 'c']));;

List.filter
  (fun (cp, gamma, out_trans) -> cp = 6 && matches_top_stack_symbol gamma ['c'; 'b'; 'c'])
  delta
*)
