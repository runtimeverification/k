kmod STRICT-JAVASCRIPT-SYNTAX 
	is including PL-INT + PL-FLOAT + PL-STRING + PL-ID
	
	syntax Name ::= Id
	
	syntax Label ::= Id
	
	syntax Exp ::= Literal
			--- | ( Exp )
			| TargetExp | InvocationExp 
			| NewExp | DeleteExp 
			| UnaryExp | BinaryExp | TernaryExp 
	
	syntax Literal ::= Bool | Int | String | Float 
			| ObjectLiteral | ArrayLiteral --- | FunctionLiteral
	
	
	syntax TargetExp ::= Name | RefinementExp
	
	syntax RefinementExp ::=  
			  Exp . Name   [prec 13 strict]
			| Exp [ Exp ]  [prec 13 strict]
	
	syntax InvocationExp ::= 
			  Exp ( ) [prec 13 strict]
			| Exp ( List{CommaElem} ) [prec 13 strict] --- Arguments
	
	syntax Argument ::= Exp
	 
	--- syntax Arguments ::= List{CommaElem}
	
	syntax NewExp ::= new InvocationExp [prec 17 strict]

	syntax DeleteExp ::= delete TargetExp [prec 19 strict]
	
	
	syntax UnaryExp ::=
			  typeof Exp [prec 19 strict]
			| `! Exp     [prec 19 strict]
			| + Exp      [prec 19 strict]
			| - Exp      [prec 19 strict]

	syntax BinaryExp ::= 
			  Exp * Exp  [prec 21 gather (E e) format(d b o d) strict]
			| Exp / Exp  [prec 21 gather (E e) format(d b o d) strict]
			| Exp % Exp  [prec 21 gather (E e) format(d b o d) strict]

			| Exp + Exp  [prec 23 gather (E e) format(d b o d) strict]
			| Exp - Exp  [prec 23 gather (E e) format(d b o d) strict]

			| Exp <  Exp [prec 25 format(d b o d) strict] --- strict(1)
			| Exp <= Exp [prec 25 format(d b o d) strict] --- strict(1)
			| Exp >  Exp [prec 25 format(d b o d) strict] --- strict(1)
			| Exp >= Exp [prec 25 format(d b o d) strict] --- strict(1)
			| Exp in Exp [prec 25 format(d b o d) strict]
			| Exp instanceof Exp [prec 25 format(d b o d) strict]

			| Exp ==  Exp [prec 27 format(d b o d) strict]
			| Exp !=  Exp [prec 27 format(d b o d) strict]
			| Exp === Exp [prec 27 format(d b o d) strict]
			| Exp !== Exp [prec 27 format(d b o d) strict]

			| Exp && Exp [prec 29 format(d b o d) strict]

			| Exp || Exp [prec 31 format(d b o d) strict]

	syntax TernaryExp ::= 
			  Exp `? Exp : Exp [prec 33 gather(e & E) format (d b o b o d) strict(1)]



	syntax RValue ::= Exp | AssignmentClause

	syntax SimpleAssignmentClause ::= Name = Exp [prec 40 gather(e E) strict(2)] --- gather(e &)

	syntax AssignmentClause ::= SimpleAssignmentClause
			| TargetExp  = RValue [prec 40 gather(e E) strict]
			| TargetExp += RValue [prec 40 gather(e E) strict]
			| TargetExp -= RValue [prec 40 gather(e E) strict]
			| TargetExp *= RValue [prec 40 gather(e E) strict]
			| TargetExp /= RValue [prec 40 gather(e E) strict]


	
	syntax ActionClause ::= InvocationExp | DeleteExp | AssignmentClause


	syntax Clause ::= ActionClause | DisruptiveClause
		
	syntax DisruptiveClause ::= ReturnClause | BreakClause | ThrowClause 
	
	syntax ReturnClause ::= return 
			| return Exp [prec 50 strict]
	
	syntax BreakClause ::= break 
			| break Label [prec 50 strict]
	
	syntax ThrowClause ::= throw Exp [prec 50 strict]


	syntax EmptyStmt ::=  ;

	syntax ExecutionStmts ::=  
			  Fragment ; [prec 90]
			| List{Fragment} ; [prec 90]
	
	syntax IfStmt ::= 
			  if ( Exp ) { Stmt } [prec 100 strict(1)]
			| if ( Exp ) { Stmt } else { Stmt } [prec 100 strict(1)]
			| if ( Exp ) { Stmt } else IfStmt [prec 100 strict(1)]
	
	syntax TryStmt ::= try { Stmt } catch ( Name ) { Stmt } [prec 100]

	syntax Stmt ::= EmptyStmt | ExecutionStmts | IfStmt | TryStmt | SwitchStmt
	
	
	syntax CommaElem ::= Exp | Property | Argument | --- ActionClause | VarDeclaration | Parameter

	syntax List{CommaElem} ::= CommaElem | .List{CommaElem} 
			| List{CommaElem} , List{CommaElem} [prec 82 assoc id: .List{CommaElem}]


	syntax ArrayLiteral ::= [ List{CommaElem} ]
	
	syntax ObjectLiteral ::= { List{CommaElem} } --- { Properties }

	--- syntax Properties ::= List{CommaElem}

	syntax PropertyName ::= String | Name 

	syntax Property ::= PropertyName : Exp [prec 80 strict]

	



	syntax CaseMatch ::= Exp 
			| CaseMatch : case CaseMatch [prec 75 gather(e E) strict]
	
	syntax Case ::= case CaseMatch : List{Fragment} [prec 70 gather(& e) strict(1)]

	syntax SwitchStmt ::= 
			  switch ( Exp ) { List{Fragment} } [prec 100 strict(1)]
---			| switch ( Exp ) { List{Fragment} ; DefaultCase } [prec 100 strict(1)]
	
---	syntax DefaultCase ::= default : List{Fragment} [prec 90 gather(e)]


	syntax Fragment ::= Clause | Case
	
	syntax List{Fragment} ::= Fragment | .List{Fragment} --- | ExitingClauses
			| List{Fragment} ; List{Fragment} [prec 82 assoc id: .List{Fragment}]


			--- syntax Case ::= 
			--- 		  case CaseMatch : List{Fragment} ; break [prec 77 gather(e &) strict(1)]
			--- 		| case CaseMatch : List{Fragment} ; break Label [prec 77 gather(e & e) strict(1)]
			--- 		| case CaseMatch : break [prec 77 gather(e) strict(1)]
			--- 		| case CaseMatch : break Label [prec 77 gather(e e) strict(1)]

			--- syntax Case ::= 
			--- 		  case CaseMatch : List{Fragment} ; DisruptiveClause [prec 77 gather(e & e) strict(1)]
			--- 		| case CaseMatch : DisruptiveClause [prec 77 gather(e e) strict(1)]

			--- syntax SwitchStmt ::= 
			--- 		  switch ( Exp ) { ExecutionStmts } [prec 95 gather(e &) strict(1)]
			--- 		| switch ( Exp ) { List{Fragment} ; DefaultCase } [prec 95 gather(e & e) strict(1)]
			--- 
			--- syntax DefaultCase ::= default : ExecutionStmts [prec 90 gather(e)]
			--- ExecutionSequence


	--- syntax NeList{Fragment} ::= Fragment 
	--- 		| NeList{Fragment} List{Fragment} [prec 111 gather(e E) id: .List{Fragment}]
	--- 		| List{Fragment} NeList{Fragment} [prec 111 gather(e E) id: .List{Fragment}]

	--- syntax List{ExecutionStmt} ::= ExecutionStmt | .List{ExecutionStmt} 
	--- 		| List{ExecutionStmt} List{ExecutionStmt} [prec 111 gather(e E) id: .List{ExecutionStmt}]



	
	--- c E : S
	--- c E :c E : S
	--- c E :c E :c E : S
	--- 
---	syntax Property ::= PropertyName : Exp

	--- syntax CaseExp ::= Exp 
	--- 
	--- syntax List{CaseExp} ::= CaseExp
	--- 		| List{CaseExp} : case List{CaseExp}

	--- syntax Case ::= case Exp : List{ExecutionStmt}
	--- 	| case List{CaseExp} : List{ExecutionStmt}


	--- syntax CaseMatch ::= case Exp  
	--- 
	--- syntax List{CaseMatch} ::= CaseMatch
	--- 		| List{CaseMatch} : List{CaseMatch}
	--- 
	--- syntax Case ::= List{CaseMatch} : List{ExecutionStmt}

	
	--- syntax ExitingCase ::= Case DisruptiveStmt
	--- 
	--- syntax DefaultCase ::= default : List{ExecutionStmt}
	--- 
	--- syntax List{ExitingCase} ::= ExitingCase
	--- 		| List{ExitingCase} List{ExitingCase}
	--- 
	--- syntax List{Case} ::= Case
	--- 		| List{ExitingCase} Case
	--- 		| List{ExitingCase} DefaultCase
	--- 
	--- syntax SwitchStmt ::= switch ( Exp ) { List{Case} } 


	--- syntax Block ::= { List{ExecutionStmt} }
	--- 
	--- syntax IfStmt ::= 
	--- 		  if ( Exp ) Block
	--- 		| if ( Exp ) else ElseClause
	--- 
	--- syntax ElseClause ::= Block | IfStmt
	--- 
	--- syntax TryStmt ::= try Block catch ( Name ) Block

endkm
