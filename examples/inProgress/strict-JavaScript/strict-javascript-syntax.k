kmod STRICT-JAVASCRIPT-SYNTAX is including PL-INT + PL-STRING + PL-ID
	syntax Name ::= Id
	
	syntax Label ::= Id
		
	syntax Exp ::= Literal
			--- | ( Exp )
			| TargetExp | InvocationExp 
			| NewExp | DeleteExp
			| UnaryExp | BinaryExp | TernaryExp
	
	syntax Literal ::= Bool | Int 
			--- | Float 
			| String | ObjectLiteral | ArrayLiteral 
			--- | FunctionLiteral


	syntax ListElement ::= Property | Exp | Argument | ActionClause | VarDeclaration | Parameter

	syntax List{ListElement} ::= NeList{ListElement}

	syntax NeList{ListElement} ::= ListElement 
			| NeList{ListElement} , List{ListElement} [prec 70 assoc id: .List{ListElement}]
			| List{ListElement} , NeList{ListElement} [prec 70 assoc id: .List{ListElement}]

	syntax List{ListElement} ::= .List{ListElement}
			| List{ListElement} , List{ListElement} [prec 70 assoc id: .List{ListElement}]



	syntax ObjectLiteral ::= { Properties }

	syntax Properties ::= List{ListElement}
	
	syntax PropertyName ::= String | Name 

	syntax Property ::= PropertyName : Exp

	syntax ArrayLiteral ::= [ List{ListElement} ]

	syntax TargetExp ::= Name | RefinementExp

	syntax RefinementExp ::=  
			  Exp . Name   [prec 23 gather(E e) strict]
			| Exp [ Exp ]  [prec 23 gather(E &) strict]

	syntax InvocationExp ::= Exp ( Arguments ) [prec 23 gather(E &) strict]
			
	syntax Argument ::= Exp
	
	syntax Arguments ::= List{ListElement}
	
	syntax NewExp ::= new InvocationExp [prec 27 strict]

	syntax DeleteExp ::= delete TargetExp [prec 29 strict]


	syntax UnaryExp ::=
			  typeof Exp [prec 29 strict]
			| `! Exp     [prec 29 strict]
			| + Exp      [prec 29 strict]
			| - Exp      [prec 29 strict]

	syntax BinaryExp ::= 
			  Exp * Exp  [prec 31 gather (E e) format(d b o d) strict]
			| Exp / Exp  [prec 31 gather (E e) format(d b o d) strict]
			| Exp % Exp  [prec 31 gather (E e) format(d b o d) strict]

			| Exp + Exp  [prec 33 gather (E e) format(d b o d) strict]
			| Exp - Exp  [prec 33 gather (E e) format(d b o d) strict]

			| Exp < Exp  [prec 37 format(d b o d) strict] --- strict(1)
			| Exp <= Exp [prec 37 format(d b o d) strict] --- strict(1)
			| Exp > Exp  [prec 37 format(d b o d) strict] --- strict(1)
			| Exp >= Exp [prec 37 format(d b o d) strict] --- strict(1)
			| Exp in Exp [prec 37 format(d b o d) strict]
			| Exp instanceof Exp [prec 37 format(d b o d) strict]

			| Exp == Exp  [prec 41 format(d b o d) strict]
			| Exp != Exp  [prec 41 format(d b o d) strict]
			| Exp === Exp [prec 41 format(d b o d) strict]
			| Exp !== Exp [prec 41 format(d b o d) strict]

			| Exp && Exp [prec 45 format(d b o d) strict]

			| Exp || Exp [prec 47 format(d b o d) strict]

	syntax TernaryExp ::= 
			  Exp `? Exp : Exp [prec 55 gather(e & E) format (d b o b o d) strict(1)] .


	syntax ActionClause ::= InvocationExp | DeleteExp | AssignmentClause



	syntax RValue ::= Exp | AssignmentClause

	syntax SimpleAssignmentClause ::= Name = Exp [prec 66 gather(e E) strict(2)] --- gather(e &)
	
	syntax AssignmentClause ::= SimpleAssignmentClause
			| TargetExp  = RValue [prec 66 gather(e E) strict]
			| TargetExp += RValue [prec 66 gather(e E) strict]
			| TargetExp -= RValue [prec 66 gather(e E) strict]
			| TargetExp *= RValue [prec 66 gather(e E) strict]
			| TargetExp /= RValue [prec 66 gather(e E) strict]

		
			
	syntax ExecutionStmt ::= EmptyStmt | ActionStmt | DisruptiveStmt 
			| SwitchStmt | IfStmt | TryStmt | IterationStmt | LabeledStmt 

	syntax List{ExecutionStmt} ::= ExecutionStmt | .List{ExecutionStmt} 
			| List{ExecutionStmt} List{ExecutionStmt} [prec 111 gather(e E) id: .List{ExecutionStmt}]

	
	syntax EmptyStmt ::=  ;
			
	syntax ActionStmt ::= ActionClause ; [prec 99 gather(e) strict]  --- gather(e) 

	syntax DisruptiveStmt ::= ReturnStmt | BreakStmt | ThrowStmt 

	syntax ReturnStmt ::= return ;
			| return Exp ;

	syntax BreakStmt ::= break ;
			| break Label ;

	syntax ThrowStmt ::= throw Exp ;



	syntax CaseMatch ::= case Exp :

	syntax List{CaseMatch} ::= CaseMatch
			| List{CaseMatch} List{CaseMatch}

	syntax Case ::= List{CaseMatch} List{ExecutionStmt}

	syntax ExitingCase ::= Case DisruptiveStmt

	syntax DefaultCase ::= default : List{ExecutionStmt}

	syntax List{ExitingCase} ::= ExitingCase
			| List{ExitingCase} List{ExitingCase}

	syntax List{Case} ::= Case
			| List{ExitingCase} Case
			| List{ExitingCase} DefaultCase

	syntax SwitchStmt ::= switch ( Exp ) { List{Case} } 


	syntax Block ::= { List{ExecutionStmt} }
	
	syntax IfStmt ::= 
			  if ( Exp ) Block
			| if ( Exp ) else ElseClause
	
	syntax ElseClause ::= Block | IfStmt

	syntax TryStmt ::= try Block catch ( Name ) Block
	
	
	syntax IterationStmt ::= 
			  while ( Exp ) Block
			| do Block while ( Exp )
			| for ( ForInitializations ; ForCondition ; ForIncrements ) Block
	
	syntax ForInitializations ::= List{ListElement}

	syntax ForCondition ::= .ForCondition | Exp 
	
	syntax ForIncrements ::= List{ListElement}
	
	syntax LabeledStmt ::= 
			  Label : SwitchStmt
			| Label : IterationStmt



	syntax VarDeclaration ::= Name | SimpleAssignmentClause
	
	syntax VarDeclarations ::= NeList{ListElement}

	syntax VarDeclarationStmt ::= var VarDeclarations ; [prec 88] 

	syntax List{VarDeclarationStmt} ::= VarDeclarationStmt | .List{VarDeclarationStmt} 
			| List{VarDeclarationStmt} List{VarDeclarationStmt} [prec 111 gather(e E) id: .List{VarDeclarationStmt}]
	
	syntax Parameter ::= Name
	
	syntax Parameters ::= List{ListElement} 
	--- 
	syntax FunctionLiteral ::= 
				  function ( Parameters ) { Program }
				| function Name ( Parameters ) { Program }
		
	syntax FunctionStmt ::= FunctionLiteral ;

	syntax List{FunctionStmt} ::= FunctionStmt | .List{FunctionStmt} 
			| List{FunctionStmt} List{FunctionStmt} [prec 111 gather(e E) id: .List{FunctionStmt}]
	
	syntax Program ::= List{VarDeclarationStmt} List{FunctionStmt} List{ExecutionStmt}
	
	syntax Stmt ::= VarDeclarationStmt | FunctionStmt | ExecutionStmt
	
	
endkm


--- https://developer.mozilla.org/en/Core_JavaScript_1.5_Reference/Operators/Operator_Precedence


kmod STRICT-JAVASCRIPT-DESUGARED-SYNTAX is 
	including STRICT-JAVASCRIPT-SYNTAX 

endkm
