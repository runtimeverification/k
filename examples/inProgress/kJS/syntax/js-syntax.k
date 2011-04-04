kmod JS-NUMBER is including PL-BUILTINS
	
	syntax MaudeNumber ::= Int | Float
	syntax JSZero ::= $zero( Int )
	syntax JSNonZero ::= $n( MaudeNumber )
	syntax JSNumber ::= JSNonZero | JSZero
	syntax JSInfinity ::= $infinity( Int )
	syntax JSQuantity ::= JSNumber | JSInfinity
	syntax JSNaN ::= $nan
	---syntax JSNumericConcept ::= JSNaN | JSInfinity
	syntax JSNumeric ::= JSQuantity | JSNaN
	
	syntax Int ::= sign( JSQuantity )
	syntax Float ::= floatValue( JSNumber )
	
	macro sign($zero(I)) 			= 	I
	macro sign($infinity(I)) 		= 	I
	macro sign($n(N:MaudeNumber)) 	= 	if floatValue($n(N)) >=Float 0.0 then 1 else -1 fi
	
	macro floatValue($n(F:Float))			= F
	macro floatValue($n(I:Int))			= Int2Float(I)
	macro floatValue($zero(I))			= 0.0
---	macro numericValue($infinity(I:Int))	= if I >=Int 0 then Infinity else -Infinity fi

	macro $n(0) 		= $zero(1)
	macro $n(0.0) 		= $zero(1)
---	macro $n(-0.0) 		= $zero(-1)
	--- macro $n(Infinity) 	= $infinity(1)
	--- macro $n(-Infinity) = $infinity(-1)
endkm

kmod JS-PRIMITIVES is including JS-NUMBER

	syntax Bool ::= boolValue( JSBoolean )
	
	syntax JSBoolean ::= $b( Bool )
	syntax JSString ::= $s( String )
	syntax JSUndefined ::= $undefined
	syntax JSNull ::= $null
	syntax JSNone ::= JSUndefined | JSNull
	syntax JSPrimitive ::= JSNone | JSBoolean | JSString | JSNumeric
	
	macro boolValue($b(B:Bool)) = B
endkm

kmod JS-SYNTAX is including JS-PRIMITIVES + K

	syntax JSObject ::= $regex( String ) | $o( List{K} ) --- | #function!!!
	syntax JSValue ::= JSPrimitive | JSObject
	syntax JSNonNumeric ::= JSObject | JSNone | JSBoolean | JSString
	syntax JSNonString ::=  JSObject | JSNone | JSBoolean | JSNumeric
	syntax JSNonNaN ::= 	JSNonNumeric | JSQuantity
	syntax JSNonNumber ::=  JSNonNumeric | JSInfinity | JSNaN
	syntax JSBooleanPlus ::=  JSBoolean | JSUndefined
	

	---syntax List{JS} ::= JS | .List{JS} | List{JS} , List{JS} [assoc id: .List{JS}]
	
	syntax K ::= 
			JSValue | .none 
		|	#this
		|	#nop
		|	#id ( String ) 
		| #staticAccess ( K , K ) [strict] 		--- Exp . Name
		| #dynamicAccess ( K , K ) [strict] 		--- Exp [ Exp ]
		| #invocation ( K , K ) [strict] 	--- Exp ( CommaList )
		
		| #new ( List{K} ) [strict]					--- new InvocationExp
		
		| #inc ( K , Bool ) [strict]				--- ++exp OR exp++
		| #dec ( K , Bool ) [strict]				--- --exp OR exp--
		
		| #delete ( K ) [strict]				--- delete TargetExp
		
		| #typeof ( K ) [strict]				--- typeof Exp
		| #not ( K ) [strict]				--- ! Exp
		| #neg ( K ) [strict] 				--- - Exp
		| #plus ( K ) [strict] 				--- + Exp
		
		| #mul ( K , K ) [strict] 			--- Exp * Exp
		| #div ( K , K ) [strict] 			--- Exp / Exp
		| #mod ( K , K ) [strict] 			--- Exp % Exp
		
		| #add ( K , K ) [strict]			--- Exp + Exp
		| #sub ( K , K ) [strict] 			--- Exp - Exp
		
		| #lt ( K , K ) [strict] 			--- Exp < Exp
		| #lte ( K , K ) [strict] 			--- Exp <= Exp
		| #gt ( K , K ) [strict] 			--- Exp > Exp
		| #gte ( K , K ) [strict] 			--- Exp >= Exp
		| #in ( K , K ) [strict]				--- Exp in Exp
		| #instanceof ( K , K ) [strict] 	--- Exp instanceof Exp
		
		| #sameAs ( K , K ) [strict] 		--- Exp == Exp
		| #notSameAs ( K , K ) [strict] 		--- Exp != Exp
		| #identical ( K , K ) [strict] 		--- Exp === Exp
		| #notIdentical ( K , K ) [strict] 	--- Exp !== Exp
		
		| #and ( K , K ) [strict] 			--- Exp && Exp
		
		| #or ( K , K ) [strict] 			--- Exp || Exp
		
		| #ternary ( K , K , K ) [strict(1)]	--- Exp ? Exp : Exp
		
		
		| #assignment ( K , K , K ) [strict]  --- TargetExp AssignmentOp Exp
		
		| #arrayLit ( List{K} ) [strict]				--- [ CommaList{Exp} ]
		| #objectLit ( List{K} ) [strict]			--- { CommaList{Property} }
		| #propertyLit ( K , K ) [strict]	--- PropertyName : Exp
		
		| #return ( K ) [strict]				--- return Exp | .
		| #break ( K ) [strict] 				--- break Label | .
		| #continue ( K ) [strict] 				--- continue Label | .
		| #throw ( K ) [strict]				--- throw Exp
		| #label ( String , K ) 
		
		| #exp ( K ) [strict]				--- exp
		
		| #stmts ( List{K} ) 		--- List{Stmt}
		| #block ( List{K} )
		| #comma ( List{K} )
		| #ifElse ( K , K , K ) [strict(1)]	--- if (Exp) Block Block
		| #try ( K , List{K} , K ) [strict]	--- 
		| #catch ( K , K )
		
		| #case ( K , K ) [strict(1)]	 	--- case Exp : Stmt
		| #default ( K ) 					--- default : Stmt
		
		| #switch ( K , List{K} , Int ) [strict(1)]	
			--- switch (Exp) { List{Case} ; DefaultCase }
		| #for ( K , K , K , K ) [strict(1)]		
			--- for ( Inits ; Cond ; Incrs ) Block
		| #forIn ( K , K , K ) [strict(2)]
			--- for ( Name in Exp ) Block
		| #while ( K , K )
			--- while ( Exp ) Block
		| #do ( K , K )
			--- do Block while ( Exp )
			
		| #labelledStmt ( K , K )	
			--- Label : Stmt
		
		| #varDeclarations ( List{K} ) [strict]
		
		| #function ( Int , K , List{K} , K )
			--- function ( Parameters ) { Program }
			--- function Name ( Parameters ) { Program }

		| #program ( List{K} )
			--- List{VarDeclarationStmt} List{FunctionStmt} List{ExecutionStmt}
endkm
			
			
