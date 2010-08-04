--- This file needs to be processed by the K-Maude tool

in ../../../../k-prelude
load strict-javascript-syntax.k
load strict-javascript-programs.k


kmod STRICT-JAVASCRIPT-SEMANTICS is including STRICT-JAVASCRIPT-SYNTAX + K
	syntax Builtin ::= String
	
	syntax KResult ::= Bool | Int | Float | String
	syntax K ::= Name | Label
			| Exp | Literal
			| CommaElem | List{CommaElem}
			| ObjectLiteral --- | Properties 
			| PropertyName | Property	
			| ArrayLiteral
			| TargetExp | RefinementExp
			| InvocationExp | Argument --- | Arguments
			| NewExp | DeleteExp
			| UnaryExp | BinaryExp | TernaryExp
			| RValue | SimpleAssignmentClause | AssignmentClause
			| ActionClause | Clause | DisruptiveClause
			| List{Fragment} | Fragment
			| ReturnClause | BreakClause | ThrowClause 
			| EmptyStmt | ExecutionStmts
			--- | ExecutionSequence --- 
			| IfStmt | TryStmt | SwitchStmt | Stmt
			| Case | CaseMatch
			
	configuration
		<T>
			<k> .K </k>
			<state> .Map </state>
	    	<I/O>
				<in> .List </in>
				<out> .List </out>
			</I/O>
		</T>

---  rule <k>X:Id => I:Int<_/k> <state_>X|->I<_/state> 
---  rule I1:Int + I2:Int => I1 +Int I2
endkm

kmod STRICT-JAVASCRIPT is including STRICT-JAVASCRIPT-PROGRAMS + STRICT-JAVASCRIPT-SEMANTICS 
  --- syntax Bag ::= [[ KLabel ]] | pgm
  --- macro [[KL:KLabel]] = <T_> <k> KL(.List{K}) </k> <_/T>
  --- macro pgm = [['sumPgm]]
endkm

