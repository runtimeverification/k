in ../../../k-prelude
in strict-javascript-syntax
in strict-javascript-programs

kmod STRICT-JAVASCRIPT-SEMANTICS is 
	including STRICT-JAVASCRIPT-DESUGARED-SYNTAX + K ---+ PL-CONVERSION 

	syntax KResult ::= Int | Bool | String
	
	syntax K ::= Name 
		---1 | Exp 
		---2 | Literal 
		---2 | ListElement | List{ListElement}
		---2 | ObjectLiteral | PropertyName | Property | ArrayLiteral
		---2 | PropertyExp | InvocationExp
		---2 | NewExp | DeleteExp 
		---2 | UnaryExp | BinaryExp | TernaryExp 
		---2 | ExpressionClause | RValueClause | AssignmentClause
		---2 | Stmt | List{Stmt}
		---2 | DisruptiveStmt | ReturnStmt | BreakStmt | ThrowStmt 
		---2 | CaseClause | List{CaseClause}
		---2 | CaseStmt | ExitingCaseStmt | DefaultCaseStmt 
		---2 | List{ExitingCaseStmt} | List{CaseStmt}
		---2 | SwitchStmt
		---2 | Block | IfStmt | ElseStmt
		
	configuration
		<T>
			<k> .K </k>
			<state> .Map </state>
	    	<I/O>
				<in> .List </in>
				<out> .List </out>
			</I/O>
		</T>
endkm

kmod STRICT-JAVASCRIPT is 
	including STRICT-JAVASCRIPT-SEMANTICS + STRICT-JAVASCRIPT-PROGRAMS 
---  syntax Bag ::= [[ KLabel ]] ---| pgm
  --- macro [[KL:KLabel]] = <T_> <k> KL(.List{K}) </k> <_/T>
  --- macro pgm = [['sumPgm]]
endkm
