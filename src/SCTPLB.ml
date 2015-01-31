open ListMore;;

type second_order_var = LogicIdentifier of string

(* here 'b is the type of atomic predicates *)
type 'b t =
  | Atomic  of ('b)
  | RatExpr	   (* discard ! *)
  | Exists	of second_order_var * ('b t)
  | Forall	of second_order_var * ('b t)
  | And	of ('b t) * ('b t)
  | Or	of ('b t) * ('b t)
  | Not	of ('b t)
  | AX	of ('b t)
  | EX	of ('b t)
  | AU	of ('b t) * ('b t)
  | EU	of ('b t) * ('b t)
  | AXB	of ('b t)
  | EXB	of ('b t)
  | AUB	of ('b t) * ('b t)
  | EUB	of ('b t) * ('b t)

let subformulas f =
  let rec aux f = match f with
  | Atomic x       -> [Atomic x]
  | RatExpr        -> failwith "not managed RatExpr in subform fun"
  | Exists (v, f') -> f :: aux f'
  | Forall (v, f') -> f :: aux f'
  | And (f1, f2)   -> f :: (aux f1 @ aux f2)
  | Or (f1, f2)    -> f :: (aux f1 @ aux f2)
  | Not (f')       -> f :: aux f'
  | AX (f')        -> f :: aux f'
  | EX (f')        -> f :: aux f'
  | EU (f1, f2)    -> f :: (aux f1 @ aux f2)
  | AU (f1, f2)    -> f :: (aux f1 @ aux f2)
  | AXB (f')        -> f :: aux f'
  | EXB (f')        -> f :: aux f'
  | EUB (f1, f2)    -> f :: (aux f1 @ aux f2)
  | AUB (f1, f2)    -> f :: (aux f1 @ aux f2) in
  ListMore.uniq (aux f)
;;
