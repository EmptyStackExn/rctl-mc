(*
#load "Fixpoint.cmo";;
*)
open Fixpoint

type 'a formula =
  | Literal of ('a)
  | And     of ('a formula) * ('a formula)
  | Or      of ('a formula) * ('a formula)
  | Not     of 'a formula

let or_normal_form (f : 'a formula) =
  let rec or_associativity (f : 'a formula) = match f with
    | Literal x -> Literal x
    | Or (Or (f1, f2), f3) ->
      Or (
	or_associativity f1,
	Or (or_associativity f2, or_associativity f3))
    | Or (f1, f2) ->
      Or (or_associativity f1, or_associativity f2)
    | And (f1, f2) ->
      And (or_associativity f1, or_associativity f2)
    | Not (f') ->
      Not (or_associativity f')
  in Fixpoint.fp (or_associativity) f
;;

let and_normal_form (f : 'a formula) =
  let rec and_associativity (f : 'a formula) = match f with
    | Literal x -> Literal x
    | And (And (f1, f2), f3) ->
      And (
	and_associativity f1,
	And (and_associativity f2, and_associativity f3))
    | And (f1, f2) ->
      And (and_associativity f1, and_associativity f2)
    | Or (f1, f2) ->
      Or (and_associativity f1, and_associativity f2)
    | Not (f') ->
      Not (and_associativity f')
  in Fixpoint.fp (and_associativity) f
;;

let dnf_of_formula (f : 'a formula) =
  let rec and_or_distributivity_rewriting (f : 'a formula) = match f with
  | Literal x    ->
    Literal x
  | And (f1, Or (f2, f3)) ->
    Or (And (f1, f2), And (f1, f3))
  | And (Or (f2, f3), f1) ->
    Or (And (f1, f2), And (f1, f3))
  | And (f1, f2) ->
    And (and_or_distributivity_rewriting f1,
	 and_or_distributivity_rewriting f2)
  | Or (f1, f2)  ->
    Or (and_or_distributivity_rewriting f1,
	and_or_distributivity_rewriting f2)
  | Not (f')     ->
    Not (and_or_distributivity_rewriting f') in
  let f_inf = Fixpoint.fp (and_or_distributivity_rewriting) f in
  or_normal_form (and_normal_form f_inf)
;;


let phi = (And (Or (Literal 4, Literal 5), Or (Literal 6, Literal 7)));;
(*
let u0 = and_or_distributivity_rewriting phi;;
let u1 = and_or_distributivity_rewriting u0;;
*)

dnf_of_formula phi;;

let dnf_clause_system_of_formula (f : 'a formula) =
  let dnf_phi = dnf_of_formula f in
  let rec and_morphism phi = match phi with
    | Literal x -> [x]
    | And (Literal x1, phi') -> x1 :: (and_morphism phi')
    | Not _ -> failwith "Not managed case of negation"
    | _     -> failwith "Formula is not in DNF form ! Or operator appeared in conjunctions"
  and or_morphism phi = match phi with
    | Literal x        -> [[x]]
    | Or (phi', phi'') -> (or_morphism phi') @ (or_morphism phi'')
    | And _            -> [and_morphism phi]
    | Not _            -> failwith "Not managed case of negation"
  in or_morphism dnf_phi
;;

let rec formula_of_dnf_clause_system s =
  let rec and_formula_of_dnf_clause c = match c with
    | l :: l' :: [] -> And (Literal l, Literal l')
    | l :: []       -> Literal l
    | []            -> failwith "Please, get out !"
    | l :: c'       -> And (Literal l, and_formula_of_dnf_clause c')
  in  match s with
  | dnfc :: dnfc' :: [] -> Or (and_formula_of_dnf_clause dnfc, and_formula_of_dnf_clause dnfc')
  | dnfc :: []          -> and_formula_of_dnf_clause dnfc
  | []                  -> failwith "God, please kill the one who reached this place!"
  | dnfc :: s'          -> Or (and_formula_of_dnf_clause dnfc, formula_of_dnf_clause_system s')
;;

let u1 = dnf_clause_system_of_formula phi;;

formula_of_dnf_clause_system u1;;
