kmod JSON-INFIX
 	is including JS-SYNTAX + JSON

	vars Obj Element Left Right : JsonObject .
	vars Elements Remaining Others Before Between  After : List{JsonElem} .
	vars Value : JsonValue .
	vars N : Number .
	vars I : Int . 
	vars Name S : String .
	vars Flag : Bool .
	
	syntax Id ::= type | children | name | value | expression | assignOp | postfix 
		
	
	macro { type : SCRIPT Between children : Elements After } = program(Elements)
	
	macro { type : VAR Between children : Elements After } = varDeclarations(Elements)
	
	macro { type : IDENTIFIER Between name : Name After } = id(Name)
	
	macro { type : SEMICOLON, expression : Elements After } = stmts(Elements)
	
	macro { type : ASSIGN Between assignOp : null Others children : (Left Right) After } 
		= assignment(null, Left, Right)

	macro { type : ASSIGN Between assignOp : Index Others children : (Left Right) After } 
		= assignment(OpValue, Left, Right)
	
	macro { type : PLUS Between (children : Left Right) After } = add(Left Right)
	macro { type : DOT Between (children : Left Right) After } = add(Left Right)
	macro { type : OR Between (children : Left Right) After } = add(Left Right)
	
	macro { type : INCREMENT Between (children : Element) Others postfix : Flag After } 
		= inc(Element, Flag)

	macro { type : INCREMENT Between (children : Element) After } = inc(Element, false)

	macro { type : DECREMENT Between (children : Element) Others postfix : Flag After } 
		= dec(Element, Flag)

	macro { type : DECREMENT Between (children : Element) After } = dec(Element, false)

	
	macro { type : ARRAY_INIT Between children : Elements After } = arrayLit(Elements)
	macro { type : NUMBER Between value : N } = n(N)
	macro { type : STRING Between value : S } = s(S)
	
	syntax Value ::= b( Bool ) | n( Number ) | s( String )
	