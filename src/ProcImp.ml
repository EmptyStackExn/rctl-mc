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


    (* mise en forme normale des suites d'instructions par associativité de ";" : (s1 ; s2) ; s3 -> s1 ; (s2 ; s3)*)
    let rec sequence_normal_form (s : statement) =
      let rec fonctional s = match s with
	| Skip      		 -> s
	| Halt  		 -> s
	| Sequence (s1, s2)	 -> (match (s1, s2) with
	    | (Sequence (s1', s2'), s3') -> Sequence (fonctional s1', Sequence (fonctional s2', fonctional s3'))
	    | (s1', s2')                 -> Sequence (s1', fonctional s2')  (* BUG : pourquoi pas fonctionnal de s1' ? *)
	)
	| Assignment _            -> s
	| FunCallStmt _		  -> s
	| IfThenElse (be, s1, s2) -> IfThenElse (be, sequence_normal_form s1, sequence_normal_form s2)
	| While (be, s)	          -> While (be, sequence_normal_form s)
	| Return _          	  -> s
      in
      Fixpoint.fp (fonctional) s

    (* programmes de test *)
    let p0 = Program (
      [FunDef (Identifier ("main"),
	       [],
               Halt);
       FunDef (Identifier ("f"),
	       [],
               Sequence (
		 Sequence (Assignment (Identifier "x", Integer 5),
			   Skip),
		 Halt))])

    let p1 = Program (
      [FunDef (Identifier ("main"),
	       [],
               Sequence (
		 IfThenElse(
		   Eq (VariableEval (Identifier "x"), Integer 0),
		   Sequence (
		     FunCallStmt (Identifier "f1", []),
		     FunCallStmt (Identifier "f2", [])),
		   Sequence (
		     FunCallStmt (Identifier "g1", []),
		     FunCallStmt (Identifier "g2", []))),
		 Skip));
      ])

    let p2 = Program (
      [FunDef (Identifier ("main"),
	       [],
               Sequence (
		 While(
		   Eq (VariableEval (Identifier "x"), Integer 0),
		   Sequence (
		     FunCallStmt (Identifier "f1", []),
		     FunCallStmt (Identifier "f2", []))),
		 Skip));
      ])

    let p3 = Program (
      [FunDef (Identifier ("main"),
	       [],
               Sequence (
		 Skip,
		 Sequence (
		   FunCallStmt (Identifier "f", []),
		   Skip)));
       FunDef (Identifier ("f"),
	       [],
	       Sequence (
		 Skip,
		 Return (Integer 5)))])

  end
;;

(* forme de  prédicats atomiques de ProcImp *)
type procimp_atomic_predicate =
  | Is_stmt  of AST.statement
  | Has_expr of AST.expression
  | Trans    of AST.expression
  | Conlit   of int
  | Def	     of AST.identifier
  | Use	     of AST.identifier

