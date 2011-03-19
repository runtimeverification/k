load js-syntax.k
load js-json-ast-ids.k

kmod JSON-INFIX
 	is including JS-SYNTAX + JSON + JS-JSON-AST-IDS
	
	syntax Id ::= JSJsonAstIds 
	
	macro o(type : "NUMBER" value : Num:Numeric Extra:JSProperties) = n(Num)
	macro o(type : "STRING" value : S:String Extra) = s(S)
	macro o(type : "REGEXP" value : S:String Extra) = r(S)
	macro o(type : "TRUE"  Extra) = b(true)
	macro o(type : "FALSE" Extra) = b(false)
	macro o(type : "NULL" Extra) = .null
	macro null = .undefined
	macro undefined = .undefined
	macro o(type : "THIS" Extra) = .this
	
	macro o(type : "IDENTIFIER" value : Name:String Extra) = id(Name)

	macro o(type : "DOT" children : a(Left , Right) Extra) = staticAccess(Left , Right)
	macro o(type : "INDEX" children : a(Left , Right) Extra) = dynamicAccess(Left , Right)
	
	macro o(type : "CALL" children : a(FunctionExp:JS, CommaList:JS) Extra) 
		= invocation(FunctionExp, CommaList)

	macro o(type : "NEW" children : a(Exp) Extra) = new(Exp)

	macro o(type : "INCREMENT" children : a(Exp:JS) postfix : Flag:Bool Extra) = inc(Exp, Flag)
	macro o(type : "INCREMENT" children : a(Exp) Extra) = inc(Exp, false)
	
	macro o(type : "DECREMENT" children : a(Exp) postfix : Flag Extra) = dec(Exp, Flag)
	macro o(type : "DECREMENT" children : a(Exp) Extra) = dec(Exp, false)
	
	macro o(type : "DELETE" children : a(Exp) Extra) = delete(Exp)
	
	macro o(type : "TYPEOF" children : a(Exp) Extra) = typeof(Exp)
	macro o(type : "NOT" children : a(Exp) Extra) = not(Exp)
	macro o(type : "UNARY_MINUS" children : a(Exp) Extra) = neg(Exp)
	macro o(type : "UNARY_PLUS" children : a(Exp) Extra) = plus(Exp)
	
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

	macro o(type : "ASSIGN" assignOp : OpCode:JS children : a(Left , Right) Extra) 
		= assignment(Left, OpCode, Right)

	macro o(type : "ARRAY_INIT" children : a(Exps:List{JS}) Extra) = arrayLit(Exps)
	macro o(type : "OBJECT_INIT" children : a(Exps:List{JS}) Extra) = objectLit(Exps)
	macro o(type : "PROPERTY_INIT" children : a(Left , Right) Extra) = propertyLit(Left , Right)
		
	macro o(type : "RETURN" value : Exp Extra) = return(Exp)	
	macro o(type : "BREAK" label : Name Extra) = break(Name)
	macro o(type : "BREAK" Extra) = break(.undefined)
	macro o(type : "CONTINUE" label : Name Extra) = continue(Name)
	macro o(type : "CONTINUE" Extra) = continue(.undefined)
---	macro o(type : "THROW" value : Exp Extra) = throw(Exp)

	macro o(type : "BLOCK" children : a(Stmts:List{JS}) Extra) = block(Stmts)

	macro o(type : "SEMICOLON" expression : Exp Extra) = exp(Exp)
		
	macro o(type : "LIST" children : a(Exps) Extra) = comma(Exps)
	macro o(type : "COMMA" children : a(Exps) Extra) = comma(Exps)

	macro o(type : "IF" condition : Condition:JS thenPart : Stmt:JS elsePart : OtherStmt:JS Extra) 
		= ifElse(Condition, Stmt, OtherStmt)

	macro o(type : "CASE" caseLabel : Exp statements : Stmt Extra) = case(Exp, Stmt)
	macro o(type : "DEFAULT" statements : Stmt Extra) = default(Stmt)

	macro o(type : "SWITCH" discriminant : Exp cases : a(Cases:List{JS}) defaultIndex : I Extra)
		= switch(Exp, Cases, I)
	
	macro o(type : "FOR" setup : Setup:JS condition : Condition:JS update : Exp body : Stmt Extra) 
		= for(Setup, Condition, Exp, Stmt)
	macro o(type : "FOR_IN" iterator : Left object : Right body : Stmt Extra) 
		= forIn(Left, Right, Stmt)

	macro o(type : "WHILE" condition : Condition body : Stmt Extra) = while(Condition, Stmt)
	macro o(type : "DO" condition : Condition body : Stmt Extra) = do(Condition, Stmt)

	macro o(type : "LABEL" label : Name statement : Stmt Extra) = controlLabel(Name, Stmt)

	macro o(type : "VAR" children : a(Exps) Extra) = varDeclarations(Exps)
	
	macro o(type : "FUNCTION" functionForm : I:Int name : Name params : a(Exps) body : Stmt Extra)
		= function(I, Name, Exps, Stmt)
		
	macro o(type : "SCRIPT" children : a(Stmts:List{JS}) Extra) = program(Stmts)
	
endkm	