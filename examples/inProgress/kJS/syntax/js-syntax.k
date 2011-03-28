load ../json/json.k

kmod JS-SYNTAX 
	is including JSON

	syntax Number ::= Int | Float
	syntax JSNumber ::= #n( Number ) | #zero( Int )
	syntax JSNumeric ::= JSNumber | #infinity( Int ) | #nan
	syntax JSValue ::= JSNumeric | #b( Bool ) | #s( String ) | #regex( String ) 
		| #undefined | #null | #this | #o( List{JS} )
	
	syntax JS ::= 
			.none
		|	JSValue
		|	#nop
		|	#id ( String ) 
		| #staticAccess ( JS , JS ) [strict] 		--- Exp . Name
		| #dynamicAccess ( JS , JS ) [strict] 		--- Exp [ Exp ]
		| #invocation ( JS , JS ) [strict] 	--- Exp ( CommaList )
		
		| #new ( List{JS} ) [strict]					--- new InvocationExp
		
		| #inc ( JS , Bool ) [strict]				--- ++exp OR exp++
		| #dec ( JS , Bool ) [strict]				--- --exp OR exp--
		
		| #delete ( JS ) [strict]				--- delete TargetExp
		
		| #typeof ( JS ) [strict]				--- typeof Exp
		| #not ( JS ) [strict]				--- ! Exp
		| #neg ( JS ) [strict] 				--- - Exp
		| #plus ( JS ) [strict] 				--- + Exp
		
		| #mul ( JS , JS ) [strict] 			--- Exp * Exp
		| #div ( JS , JS ) [strict] 			--- Exp / Exp
		| #mod ( JS , JS ) [strict] 			--- Exp % Exp
		
		| #add ( JS , JS ) [strict]			--- Exp + Exp
		| #sub ( JS , JS ) [strict] 			--- Exp - Exp
		
		| #lt ( JS , JS ) [strict] 			--- Exp < Exp
		| #lte ( JS , JS ) [strict] 			--- Exp <= Exp
		| #gt ( JS , JS ) [strict] 			--- Exp > Exp
		| #gte ( JS , JS ) [strict] 			--- Exp >= Exp
		| #in ( JS , JS ) [strict]				--- Exp in Exp
		| #instanceof ( JS , JS ) [strict] 	--- Exp instanceof Exp
		
		| #sameAs ( JS , JS ) [strict] 		--- Exp == Exp
		| #notSameAs ( JS , JS ) [strict] 		--- Exp != Exp
		| #identical ( JS , JS ) [strict] 		--- Exp === Exp
		| #notIdentical ( JS , JS ) [strict] 	--- Exp !== Exp
		
		| #and ( JS , JS ) [strict] 			--- Exp && Exp
		
		| #or ( JS , JS ) [strict] 			--- Exp || Exp
		
		| #ternary ( JS , JS , JS ) [strict(1)]	--- Exp ? Exp : Exp
		
		
		| #assignment ( JS , JS , JS ) [strict]  --- TargetExp AssignmentOp Exp
		
		| #arrayLit ( List{JS} ) [strict]				--- [ CommaList{Exp} ]
		| #objectLit ( List{JS} ) [strict]			--- { CommaList{Property} }
		| #propertyLit ( JS , JS ) [strict]	--- PropertyName : Exp
		
		| #return ( JS ) [strict]				--- return Exp | .
		| #break ( JS ) [strict] 				--- break Label | .
		| #continue ( JS ) [strict] 				--- continue Label | .
		| #throw ( JS ) [strict]				--- throw Exp
		| #label ( String , JS ) 
		
		| #exp ( JS ) [strict]				--- exp
		
		| #stmts ( List{JS} ) 		--- List{Stmt}
		| #block ( List{JS} )
		| #comma ( List{JS} )
		| #ifElse ( JS , JS , JS ) [strict(1)]	--- if (Exp) Block Block
		| #try ( JS , List{JS} , JS ) [strict]	--- 
		| #catch ( JS , JS )
		
		| #case ( JS , JS ) [strict(1)]	 	--- case Exp : Stmt
		| #default ( JS ) 					--- default : Stmt
		
		| #switch ( JS , List{JS} , Int ) [strict(1)]	
			--- switch (Exp) { List{Case} ; DefaultCase }
		| #for ( JS , JS , JS , JS ) [strict(1)]		
			--- for ( Inits ; Cond ; Incrs ) Block
		| #forIn ( JS , JS , JS ) [strict(2)]
			--- for ( Name in Exp ) Block
		| #while ( JS , JS )
			--- while ( Exp ) Block
		| #do ( JS , JS )
			--- do Block while ( Exp )
			
		| #labelledStmt ( JS , JS )	
			--- Label : Stmt
		
		| #varDeclarations ( List{JS} ) [strict]
		
		| #function ( Int , JS , List{JS} , JS )
			--- function ( Parameters ) { Program }
			--- function Name ( Parameters ) { Program }

		| #program ( List{JS} )
			--- List{VarDeclarationStmt} List{FunctionStmt} List{ExecutionStmt}
endkm
			
			
