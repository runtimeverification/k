load js-syntax.k

kmod JSON-INFIX
 	is including JS-SYNTAX + JSON
	
	syntax JsonTag ::= type | children | name | value | expression | assignOp | postfix 
	
	syntax Id ::= JsonTag 
	
	macro o(type : "NUMBER" value : N:Numeric Properties:JSProperties) = n(N)
	macro o(type : "STRING" value : S:String Properties) = s(S)
	macro o(type : "BOOLEAN" value : B:Bool Properties) = b(B)
	
	macro o(type : "IDENTIFIER" name : Name:String Properties) = id(Name)
	
	macro o(type : "OR" children : a(Left:JS , Right:JS) Properties) = or(Left , Right)
	
	macro o(type : "PLUS" children : a(Left , Right) Properties) = add(Left , Right)
	
	macro o(type : "INCREMENT" children : a(Element:JS) Properties) = inc(Element, false)
	macro o(type : "INCREMENT" children : a(Element) postfix : Flag:Bool Properties) = inc(Element, Flag)
	
	macro o(type : "DECREMENT" children : a(Element) Properties) = dec(Element, false)
	macro o(type : "DECREMENT" children : a(Element) postfix : Flag Properties) = dec(Element, Flag)

	
	macro o(type : "SCRIPT" children : a(Elements:List{JS}) Properties) = program(Elements)
	
	macro o(type : "VAR" children : a(Elements) Properties) = varDeclarations(Elements)
	
	macro o(type : "SEMICOLON" expression : a(Elements) Properties) = stmts(Elements)
	
	macro o(type : "DOT" children : a(Left , Right) Properties) = staticAccess(Left , Right)
	
	macro o(type : "ASSIGN" assignOp : OpCode:JS children : a(Left , Right)) 
		= assignment(OpCode, Left, Right)
	
	
	macro o(type : "ARRAY_INIT" children : a(Elements) Properties) = arrayLit(Elements)
endkm	