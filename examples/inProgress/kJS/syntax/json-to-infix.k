load js-syntax.k
load ../js-json-ast-ids.maude

kmod JSON-INFIX
 	is including JS-SYNTAX + JSON
	
	syntax Id ::= JSJsonAstIds 
	
	macro o(type : "NUMBER" value : N:Numeric Extra:JSProperties) = n(N)
	macro o(type : "STRING" value : S:String Extra) = s(S)
	macro o(type : "BOOLEAN" value : B:Bool Extra) = b(B)
	
	macro o(type : "IDENTIFIER" name : Name:String Extra) = id(Name)

	macro o(type : "DOT" children : a(Left , Right) Extra) = staticAccess(Left , Right)
	
	macro o(type : "INCREMENT" children : a(Element:JS) Extra) = inc(Element, false)
	macro o(type : "INCREMENT" children : a(Element) postfix : Flag:Bool Extra) = inc(Element, Flag)
	
	macro o(type : "DECREMENT" children : a(Element) Extra) = dec(Element, false)
	macro o(type : "DECREMENT" children : a(Element) postfix : Flag Extra) = dec(Element, Flag)
	
	macro o(type : "TYPEOF" children : a(Element) Extra) = typeof(Element)
	macro o(type : "NOT" children : a(Element) Extra) = not(Element)
	macro o(type : "??? -" children : a(Element) Extra) = neg(Element)
	macro o(type : "??? +" children : a(Element) Extra) = plus(Element)
	
	macro o(type : "MUL" children : a(Left:JS , Right:JS) Extra) = mul(Left , Right)
	macro o(type : "DIV" children : a(Left , Right) Extra) = div(Left , Right)
	macro o(type : "MOD" children : a(Left , Right) Extra) = mod(Left , Right)
	
	macro o(type : "PLUS" children : a(Left , Right) Extra) = add(Left , Right)
	macro o(type : "MINUS" children : a(Left , Right) Extra) = sub(Left , Right)

	macro o(type : "LT" children : a(Left , Right) Extra) = lt(Left , Right)
	macro o(type : "LE" children : a(Left , Right) Extra) = lte(Left , Right)
	macro o(type : "GT" children : a(Left , Right) Extra) = gt(Left , Right)
	macro o(type : "GE" children : a(Left , Right) Extra) = gte(Left , Right)
	macro o(type : "IN" children : a(Left , Right) Extra) = in(Left , Right)
	macro o(type : "INSTANCEOF" children : a(Left , Right) Extra) = instanceof(Left , Right)
		
	macro o(type : "EQ" children : a(Left , Right) Extra) = sameAs(Left , Right)
	macro o(type : "NE" children : a(Left , Right) Extra) = notSameAs(Left , Right)
	macro o(type : "STRICT_EQ" children : a(Left , Right) Extra) = identical(Left , Right)
	macro o(type : "STRICT_NE" children : a(Left , Right) Extra) = notIdentical(Left , Right)
	
	macro o(type : "AND" children : a(Left , Right) Extra) = and(Left , Right)
	
	macro o(type : "OR" children : a(Left , Right) Extra) = or(Left , Right)

	macro o(type : "HOOK" children : a(Left , Middle:JS, Right) Extra) 
		= ternary(Left , Middle, Right)

	macro o(type : "ASSIGN" assignOp : OpCode:JS children : a(Left , Right)) 
		= assignment(Left, OpCode, Right)
	
	macro o(type : "ARRAY_INIT" children : a(Elements) Extra) = arrayLit(Elements)
	
	macro o(type : "SEMICOLON" expression : a(Elements) Extra) = stmts(Elements)
	
	macro o(type : "VAR" children : a(Elements) Extra) = varDeclarations(Elements)
	
	macro o(type : "SCRIPT" children : a(Elements:List{JS}) Extra) = program(Elements)
	
endkm	