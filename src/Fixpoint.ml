(* opérateur de point fixe : convergence non assurée !*)
let rec fp (f : 'a -> 'a) (u0 : 'a) : 'a  =
  let u_n   = ref u0 in
  let f_u_n = f !u_n in
  if (!u_n = f_u_n)
  then !u_n
  else fp f f_u_n
;;
