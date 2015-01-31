open Fixpoint

module AST =
struct

    (* AST de ProcImp *)
    type identifier = Identifier of string
    type expression =
      | Plus         of (expression * expression)
      | Minus        of (expression * expression)
      | Times        of (expression * expression)
      | Integer      of int
      | VariableEval of identifier
    type boolean_expression =
      | True
      | False
      | Eq     of expression * expression
      | Leq    of expression * expression
      | And    of boolean_expression * boolean_expression
      | Not    of boolean_expression
    type statement =
      | Skip
      | Halt
      | Sequence    of (statement * statement)
      | Assignment  of (identifier * expression)
      | FunCallStmt of (identifier * (expression list))
      | IfThenElse  of (boolean_expression * statement * statement)
      | While       of (boolean_expression * statement)
      | Return      of expression
    type fundef     = FunDef of (identifier * identifier list * statement)
    type t = Program of (fundef list)

    (* parameter 'a gives type for the control point for annotation *)
    type 'a annotated_statement =
      | AnnotatedSkip        of 'a 
      | AnnotatedHalt        of 'a 
      | AnnotatedSequence    of ('a annotated_statement) * ('a annotated_statement)
      | AnnotatedAssignment  of 'a * identifier * expression
      | AnnotatedFunCallStmt of 'a * identifier * (expression list)
      | AnnotatedIfThenElse  of 'a * boolean_expression * 'a annotated_statement * 'a annotated_statement
      | AnnotatedWhile       of 'a * boolean_expression * 'a annotated_statement
      | AnnotatedReturn      of 'a * expression


(* forme de  prédicats atomiques de ProcImp *)
type procimp_atomic_predicate =
  | Is_stmt  of AST.statement
  | Has_expr of AST.expression
  | Trans    of AST.expression
  | Conlit   of int
  | Def	     of AST.identifier
  | Use	     of AST.identifier

