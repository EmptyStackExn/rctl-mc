let uniq l =
  let rec aux l acc = match l with 
    | e :: l' ->
      if List.exists (fun x -> x = e) acc
      then aux l' acc
      else aux l' (e :: acc)
    | [] -> acc
  in List.rev (aux l [])
;;

let double_uniq ll =
  uniq (List.map (uniq) ll)
;;

let cartesian_product (l1 : 'a list) (l2 : 'b list) =
  let l1_times_l2 = ref [] in
  let () = List.fold_left
    (fun _ x1 -> List.fold_left
      (fun _ x2 -> l1_times_l2 := !l1_times_l2 @ [(x1, x2)])
      ()
      l2)
    ()
    l1 in
  !l1_times_l2
;;

(* from a binary relation A × B, returns a function A -> 2^B *)
let factor_merge_assoc assoc_list =
  let domain = uniq (List.map (fun (x, y) -> x) assoc_list) in
  let merged_assoc_list = ref [] in
  let () = List.fold_left
    (fun _ x ->
      let y_set = List.map (snd) (List.filter (fun (x', _) -> x = x') assoc_list) in
      merged_assoc_list := !merged_assoc_list @ [(x, y_set)]
    )
    ()
    domain in
  !merged_assoc_list
;;
