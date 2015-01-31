
let s1 = ProcImp.AST.Sequence (
  ProcImp.AST.Assignment (ProcImp.AST.Identifier "x", ProcImp.AST.Integer 5),
  ProcImp.AST.Halt);;

let s0 = ProcImp.AST.Sequence (
  ProcImp.AST.Assignment (ProcImp.AST.Identifier "x", ProcImp.AST.Integer 5),
  ProcImp.AST.Sequence (
    ProcImp.AST.FunCallStmt (ProcImp.AST.Identifier "f", []),
    ProcImp.AST.Halt));;

let p0 =
  ProcImp.AST.Program (
    [ProcImp.AST.FunDef (
      ProcImp.AST.Identifier "main",
      [],
      s0)])
;;


let model0 = pds_cfg_of_program p0;;
let phi_0 = SCTPLB.And (
  SCTPLB.Atomic (ProcImp.Def (ProcImp.AST.Identifier "x")),
  SCTPLB.EX (SCTPLB.Atomic (ProcImp.Is_stmt ProcImp.AST.Halt)));;

let stack_alpha0 = stack_alphabet_of_procimp_program p0;;
let phi_0 =
  SCTPLB.EX (SCTPLB.Atomic (ProcImp.Def (ProcImp.AST.Identifier "x")));;



let c_true_ama_0 = c_true_ama_set_of_pds model0 stack_alpha0;;
let apds_prod_0 = model_formula_product_apds 
  model0
  phi_0
  stack_alpha0
;;

let pre_star_ama_0 = AMA.ama_of_pre_star apds_prod_0 (AMA.pre_states_injection (product_states_injection c_true_ama_0));;

let (_, _, test, _) = c_true_ama_0 ;;
let (_, _, test, _) = apds_prod_0;;
let (_, _, test, _) = pre_star_ama_0 ;;

let i0 = ("main", 1);;

AMA.execute
  pre_star_ama_0
  (ConcreteState (ProductConcreteState (i0, phi_0)), [ProcImp.AST.Identifier "main"])
;;

(* -------------------- *)



let s_main = ProcImp.AST.Sequence (
  ProcImp.AST.FunCallStmt (ProcImp.AST.Identifier "f", []),
  ProcImp.AST.Return (ProcImp.AST.VariableEval (ProcImp.AST.Identifier "x")))
;;

let s_f = 
  ProcImp.AST.Sequence (
    ProcImp.AST.Halt,
    ProcImp.AST.Return (ProcImp.AST.VariableEval (ProcImp.AST.Identifier "x")))
;;


let p0 =
  ProcImp.AST.Program (
    [ProcImp.AST.FunDef (
      ProcImp.AST.Identifier "main",
      [],
      s_main) ;
    ProcImp.AST.FunDef (
      ProcImp.AST.Identifier "f",
      [],
      s_f)])
;;

let phi_0 =
  SCTPLB.And (
    SCTPLB.Atomic (ProcImp.Is_stmt (ProcImp.AST.Return (ProcImp.AST.VariableEval (ProcImp.AST.Identifier "x")))),
    SCTPLB.EX (SCTPLB.Atomic (ProcImp.Is_stmt (ProcImp.AST.Halt))))
;;

let phi_1 =
  SCTPLB.EX (SCTPLB.Atomic (ProcImp.Is_stmt (ProcImp.AST.Halt)))
;;

CFG.program_model_checking_at_default_initial_control_point p0 phi_0;;
CFG.program_model_checking p0 phi_0;;

CFG.pds_cfg_of_program p0;;


(* ***************** *)



let phi_0'' =
  SCTPLB.And (
    SCTPLB.Atomic (ProcImp.Is_stmt (ProcImp.AST.Return (ProcImp.AST.VariableEval (ProcImp.AST.Identifier "x")))),
    SCTPLB.EX (SCTPLB.Atomic (ProcImp.Is_stmt (ProcImp.AST.Halt))))
;;

CFG.pds_cfg_of_program p0';;
