#load "ListMore.cmo"
#load "Fixpoint.cmo";;
#load "Prop.cmo";;
#load "ProcImp.cmo";;
#load "PDS.cmo";;
#load "APDS.cmo";;
#load "AMA.cmo";;
#load "SCTPLB.cmo";;
#load "CFG.cmo";;
open ListMore;;
open Fixpoint;;
open Prop;;
open ProcImp;;
open PDS;;
open APDS;;
open AMA;;
open SCTPLB;;
open CFG;;

let s_main = ProcImp.AST.Sequence (
  ProcImp.AST.FunCallStmt (ProcImp.AST.Identifier "f", []),
  ProcImp.AST.Halt)
;;

let s_f = 
  ProcImp.AST.Sequence (
    ProcImp.AST.Assignment (ProcImp.AST.Identifier "x", ProcImp.AST.Integer 1),
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
    SCTPLB.Atomic (ProcImp.Is_stmt (ProcImp.AST.Halt)),
    SCTPLB.EXB (SCTPLB.Atomic (ProcImp.Is_stmt (ProcImp.AST.Return (ProcImp.AST.VariableEval (ProcImp.AST.Identifier "x"))))))
;;

let phi_1 =
  SCTPLB.EUB (
    SCTPLB.Atomic (ProcImp.Is_stmt (ProcImp.AST.Halt)),
    SCTPLB.Atomic (ProcImp.Is_stmt (ProcImp.AST.Return (ProcImp.AST.VariableEval (ProcImp.AST.Identifier "x"))))
  )
;;


SCTPLB.And (
  SCTPLB.Atomic (ProcImp.Is_stmt (ProcImp.AST.Halt)),
  SCTPLB.EXB (SCTPLB.Atomic (ProcImp.Is_stmt (ProcImp.AST.Return (ProcImp.AST.VariableEval (ProcImp.AST.Identifier "x"))))))
;;

CFG.program_model_checking p0 phi_0 ("f", 2) [ProcImp.AST.Identifier "f" ; ProcImp.AST.Identifier "main"];;

