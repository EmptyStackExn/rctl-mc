(*
  'a : type of symbols of stack
  'b : type of atomic predicates
  'c : type of control_points
*)
(* here for a program in ProcImp
   'a is ProcImp.AST.identifier
   'c is string * int
*)
type 'a stack_symbol  = ('a)
type 'a stack_word    = 'a list
type 'c control_point = ('c)
type ('a, 'c) transition = 'c control_point * 'a stack_symbol * 'a stack_word * 'c control_point

(* here it's ProcImp.AST.l0_atomic_predicate *)
type 'b atomic_predicate = ('b)

type ('a, 'b, 'c) t =
    'c control_point list                                      (* list of controls point of program *) 
    * (('a, 'c) transition list)			       (* transition of the CFG *) 
    * 'c control_point list				       (* initial control points of program *) 
    * (('c control_point * (('b atomic_predicate) list)) list) (* association of a control point to a set of atomic predicates *)
