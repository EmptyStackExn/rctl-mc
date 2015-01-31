(*
#load "ListMore.cmo"
#load "Fixpoint.cmo";;
#load "Prop.cmo";;
#load "ProcImp.cmo";;
#load "PDS.cmo";;
#load "APDS.cmo";;
#load "AMA.cmo";;
#load "SCTPLB.cmo";;
#load "CFG.cmo";;
*)
open ListMore;;
open Fixpoint;;
open Prop;;
open ProcImp;;
open PDS;;
open APDS;;
open AMA;;
open SCTPLB;;
open CFG;;

let time f x =
    let t = Sys.time() in
    let fx = f x in
    Printf.printf "execution time: %fs" (Sys.time() -. t);
    fx
;;

let rec range a b =
  assert (a <= b);
  let rec aux b acc = match b with 
    | x when x = a -> x :: acc
    | _            -> aux (b - 1) (b :: acc)
  in aux b []
;;

let exp a b = int_of_float ((float_of_int a) ** (float_of_int b));;

(* height >= 1 *)
let generate_linear_example length : ('a, 'b, 'c) PDS.t =
  let states = range 1 (length + 1) in
  let transitions = ref [] in
  let () =
    List.fold_left
      (fun _ k ->
	transitions := (k, 'a', ['a'], k - 1) :: !transitions
      )
      ()
      (range 2 (length + 1)) in
  let lambda = ref [(length + 1, [2])] in
  let () =
    List.fold_left
      (fun _ k ->
	lambda := (k, [1]) ::  !lambda
      )
      ()
      (range 1 length) in
  (states, !transitions, [], !lambda)
;;

generate_linear_example 3;;

(* height >= 1 *)
let generate_exponential_example height : ('a, 'b, 'c) PDS.t =
  let states = range 1 ((exp 2 (height + 1)) - 1) in
  let transitions = ref [] in
  let () =
    List.fold_left
      (fun _ h ->
	List.fold_left
	  (fun _ k ->
	    transitions := ((exp 2 h) + k, 'a', ['a'], (exp 2 (h - 1)) + k / 2) :: !transitions
	  )
	  ()
	  (range 0 ((exp 2 h) - 1))
      )
      ()
      (range 1 height) in
  let lambda = ref [(1, [1])] in
  let () =
    List.fold_left
      (fun _ h ->
	List.fold_left
	  (fun _ k ->
	    lambda := ((exp 2 h) + k, [1]) :: !lambda
	  )
	  ()
	  (range 0 ((exp 2 h) - 1))
      )
      ()
      (range 1 (height - 1)) in
  let () = 
    List.fold_left
      (fun _ k ->
	lambda := ((exp 2 height) + k, [2]) :: !lambda
      )
      ()
      (range 0 ((exp 2 height) - 1))
  in
  (states, !transitions, [], !lambda)
;;

let height = int_of_string (Sys.argv.(1));;
let eu_phi = SCTPLB.EUB (SCTPLB.Atomic (1), SCTPLB.Atomic (2));;

let () =
  (*  for i = 2 to height do *)
    begin
      print_string "Height of transition system is " ;
      print_int height ;
      print_string " -> " ;
      flush stdout ;
      let pds = generate_exponential_example height in
      let _ = time (fun pds0 -> CFG.pds_model_checking pds0 eu_phi 1 ['a'] ['a']) pds in () ;
      print_endline "" ;
      flush stdout 
    end
  (* done *) in ()
;;
