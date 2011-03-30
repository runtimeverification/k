kmod JS-NUMBER is including PL-BUILTINS
	
	syntax MaudeNumber ::= Int | Float
	syntax JSNumber ::= $n( MaudeNumber ) | $zero( Int )
	syntax JSNumeric ::= JSNumber | $infinity( Int ) | $nan
	
	syntax Int ::= sign( JSNumeric )
	syntax Float ::= numericValue( JSNumeric )
	
	macro sign($zero(I)) 		= 	I
	macro sign($infinity(I)) 	= 	I
	macro sign(Num:JSNumeric) 	= 	if numericValue(Num) >=Float 0.0 then 1 else -1 fi
	
	macro numericValue($n(F:Float))			= F
	macro numericValue($n(I:Int))			= Int2Float(I)
	macro numericValue($zero(I))			= 0.0
	macro numericValue($infinity(I:Int))	= if I >=Int 0 then Infinity else -Infinity fi

	macro $n(0) 		= $zero(1)
	macro $n(0.0) 		= $zero(1)
---	macro $n(-0.0) 		= $zero(-1)
	macro $n(Infinity) 	= $infinity(1)
	macro $n(-Infinity) = $infinity(-1)
endkm

kmod JS-PRIMITIVES is including JS-NUMBER

	syntax Bool ::= boolValue( JSBoolean )
	
	syntax JSBoolean ::= $b( Bool )
	syntax JSString ::= $s( String )
	syntax JSPrimitive ::= $undefined | $null | JSBoolean | JSString | JSNumeric
	
	macro boolValue($b(B:Bool)) = B
endkm

kmod JS-SYNTAX is including JS-PRIMITIVES 

	syntax JSObject ::= $regex( String ) | $o( List{JS} ) --- | #function!!!
	syntax JSValue ::= JSPrimitive | JSObject
	
	syntax List{JS} ::= JS | .List{JS} | List{JS} , List{JS} [assoc id: .List{JS}]
	
	syntax JS ::= 
			JSValue | .none 
		|	#this
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
			
			
