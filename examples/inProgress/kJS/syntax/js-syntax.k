kmod JS-SYNTAX 
	is including PL-INT + PL-FLOAT + PL-STRING + PL-ID + K

	syntax Value ::= b( Bool ) | n( Number ) | s( String )
	
	syntax Number ::= Int | Float
	
	syntax List{JS} ::= JS | .List{JS}
			| List{JS}  List{JS} [assoc id: .List{JS}]
	
	syntax JS ::= id( String ) | label( String )
	
			| Value
			
			| nop
			
			| staticAccess( K , K ) [strict] 		--- Exp . Name
			| dynamicAccess( K , K ) [strict] 		--- Exp [ Exp ]
			| invocation( K , List{JS} ) [strict] 	--- Exp ( CommaList{Argument} )
			
			| new( K ) [strict]					--- new InvocationExp
			
			| delete( K ) [strict]				--- delete TargetExp
			
			| typeof ( K ) [strict]				--- typeof Exp
			| not ( K ) [strict]				--- ! Exp
			| neg ( K ) [strict] 				--- - Exp
			| plus ( K ) [strict] 				--- + Exp
			
			| mul ( K , K ) [strict] 			--- Exp * Exp
			| div ( K , K ) [strict] 			--- Exp / Exp
			| mod ( K , K ) [strict] 			--- Exp % Exp
			
			| add ( K , K ) [strict]			--- Exp + Exp
			| sub ( K , K ) [strict] 			--- Exp - Exp
			
			| lt ( K , K ) [strict] 			--- Exp < Exp
			| lte ( K , K ) [strict] 			--- Exp <= Exp
			| gt ( K , K ) [strict] 			--- Exp > Exp
			| gte ( K , K ) [strict] 			--- Exp >= Exp
			| in ( K , K ) [strict]				--- Exp in Exp
			| instanceof ( K , K ) [strict] 	--- Exp instanceof Exp
			
			| sameAs ( K , K ) [strict] 		--- Exp == Exp
			| notSameAs ( K , K ) [strict] 		--- Exp != Exp
			| identical ( K , K ) [strict] 		--- Exp === Exp
			| notIdentical ( K , K ) [strict] 	--- Exp !== Exp
			
			| and ( K , K ) [strict] 			--- Exp && Exp
			
			| or ( K , K ) [strict] 			--- Exp || Exp
			
			| ternary ( K , K , K ) [strict(1)]	--- Exp ? Exp : Exp
			
			
			| assignment ( K , K ) [strict]		--- TargetExp = Exp
			| assignment ( K , K , K ) [strict] --- TargetExp AssignmentOp Exp
			
			| arrayLit ( List{JS} ) [strict]				--- [ CommaList{Exp} ]
			| objectLit ( List{JS} ) [strict]			--- { CommaList{Property} }
			| propertyLit ( K , K ) [strict]	--- PropertyName : Exp
			
			| return ( K ) [strict]				--- return Exp | .
			| break ( K ) [strict] 				--- break Label | .
			| throw ( K ) [strict]				--- throw Exp

			| stmts ( List{JS} ) [strict]		--- List{Stmt}
			| ifElse ( K , K , K ) [strict(1)]	--- if (Exp) Block Block
			| tryCatch ( K , K , K ) [strict]	--- try Block catch (Exp) Block
			
			| case ( List{JS} , K ) [strict(1)]	 
				--- case List{CaseMatch} : List{Stmt}
			| switch ( K , List{JS} , K ) [strict(1)]	
				--- switch (Exp) { List{Case} ; DefaultCase }
			| for ( K , K , K , K ) [strict(1)]		
				--- for ( Inits ; Cond ; Incrs ) Block
			| forIn ( K , K , K ) [strict(2)]
				--- for ( Name in Exp ) Block
			| while ( K , K )
				--- while ( Exp ) Block
			| do ( K , K )
				--- do Block while ( Exp )
				
			| labelledStmt ( K , K )	
				--- Label : Stmt
			
			| varDeclarations ( List{JS} ) [strict]
			
			| function ( K , List{JS} , K )
				--- function ( Parameters ) { Program }
				--- function Name ( Parameters ) { Program }

			| program ( K )
				--- List{VarDeclarationStmt} List{FunctionStmt} List{ExecutionStmt}
endkm
			
			
