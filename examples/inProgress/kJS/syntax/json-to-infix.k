load js-syntax.k

kmod JSON-INFIX
 	is including JS-SYNTAX + JSON
	
	syntax JsonTag ::= type | children | name | value | expression | assignOp | postfix 
	
	syntax JsonTypeName ::= 
			SCRIPT | VAR | IDENTIFIER | SEMICOLON
		|	ASSIGN | PLUS | DOT | OR 
		| 	INCREMENT | DECREMENT | ARRAY_INIT 
		|	NUMBER | STRING | BOOLEAN
	
	syntax Id ::= JsonTag | JsonTypeName 
	
	macro o(type : NUMBER value : N:Number) = n(N)
	macro o(type : STRING value : S:String) = s(S)
	macro o(type : BOOLEAN value : B:Bool) = b(B)
	
	macro o(type : IDENTIFIER name : Name:String) = id(Name)
	
	macro o(type : OR children : a(Left , Right)) = or(Left Right)
	
	macro o(type : PLUS children : a(Left , Right)) = add(Left Right)
	
	macro o(type : INCREMENT children : a(Element)) = inc(Element, false)
	macro o(type : INCREMENT children : a(Element) postfix : Flag:Bool) = inc(Element, Flag)
	
	macro o(type : DECREMENT children : a(Element)) = dec(Element, false)
	macro o(type : DECREMENT children : a(Element) postfix : Flag) = dec(Element, Flag)

	
	macro o(type : SCRIPT children : Elements:List{JsonElem}) = program(Elements)
	
	macro o(type : VAR children : Elements) = varDeclarations(Elements)
	
	
	macro o(type : SEMICOLON, expression : Elements) = stmts(Elements)
	
	macro o(type : ASSIGN assignOp : OpCode:JsonTerminal children : a(Left:JS , Right:JS)) 
		= assignment(OpCode, Left, Right)
	
	macro o(type : DOT children : a(Left , Right)) = staticAccess(Left Right)
	
	
	
	macro o(type : ARRAY_INIT children : a(Element)) = arrayLit(Elements)
	

endkm	