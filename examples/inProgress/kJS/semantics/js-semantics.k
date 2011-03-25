load ../syntax/js-syntax.k

kmod JS-TYPEOF 
	is protecting JS-SYNTAX .

	macro #typeof(#undefined) 			= #s("undefined")
	macro #typeof(#null) 				= #s("object")
	macro #typeof(#b(_)) 				= #s("boolean")
	macro #typeof(Num:JSNumeric) 		= #s("number")
	macro #typeof(#s(_)) 				= #s("string")
	macro #typeof(#function(_, _, _, _))	= #s("function")
	macro #typeof(#o(_)) 				= #s("object")

	--- rule #typeof(#undefined) 			=> #s("undefined")
	--- rule #typeof(#null) 				=> #s("object")
	--- rule #typeof(#b(_)) 				=> #s("boolean")
	--- rule #typeof(Num:JSNumeric) 		=> #s("number")
	--- rule #typeof(#s(_)) 				=> #s("string")
	--- rule #typeof(#function(_, _, _, _))	=> #s("function")
	--- rule #typeof(#o(_)) 				=> #s("object")
	
endkm	


kmod JS-ARITH 
	is protecting JS-SYNTAX + PL-BUILTINS .

	syntax JS ::= arith( Id , JS , JS ) | 
		logic( Id , JS , JS ) | 
		asFloat( JS ) | asInt( JS ) | asBool( JS ) | asString( JS )
	
	macro #div(Left:JS, Right:JS) = arith("div", Left, Right)
	macro #mod(Left, Right) = arith("mod", Left, Right)
	macro #mul(Left, Right) = arith("mul", Left, Right)
	macro #add(Left, Right) = arith("add", Left, Right)
	macro #sub(Left, Right) = arith("sub", Left, Right)
	
	macro #and(Left, Right) = logic("and", Left, Right)
	macro #or(Left, Right)  = logic("or", Left, Right)
		
	
	macro asFloat(#nan) 		= #nan
	macro asFloat(#n(F:Float)) 	= F
	macro asFloat(Other:JS) 	= Int2Float(asInt(Other))

	macro asFloat( #n(F:Float) ) = F
	macro asFloat( #n(I:Int) ) 	= Int2Float(I)
	macro asFloat(#s(S:String)) = String2Float(S)
	macro asFloat(Other:JS) 	= asInt(Other)

	macro asInt(#n(F:Float)) 	= Float2Int(F)
	macro asInt(#n(I:Int)) 		= I
	macro asInt(#b(true)) 		= 1
	macro asInt(#b(false)) 		= 0
	macro asInt(#null) 			= 0
	macro asInt(#undefined) 	= 0
	macro asInt(#s(S:String)) 	= String2Int(S)
	macro asInt(Other)			= #nan

	macro asBool(#b(B:Bool)) 	= B
	macro asBool(#n(0)) 		= false
	macro asBool(#nan) 			= false
	macro asBool(#null) 		= false
	macro asBool(#undefined) 	= false
	macro asBool(#s("")) 		= false
	macro asBool(_) 			= true

---	macro asString(#s(S)) 		= #invocation(#staticAccess(newString(S),#s("toString")),#comma(.List{JS}))

	--- macro asString(#s(_)) = _
	--- macro asString(#n(_)) = string(_)
	--- macro asString(#b(true)) = "true"
	--- macro asString(#b(false)) = "false"
	--- macro asString(#null) = "null"
	--- macro asString(#undefined) = "undefined"
	--- macro asString(#nan) = "NaN"

endkm

kmod JS-SEMANTICS
	is including JS-TYPEOF + JS-ARITH
endkm


--- 
--- 	--- syntax JSArg ::= JSValue
--- 
--- 	
--- --- arithmetic expressions
--- 
--- --- arithmetic with NaN
--- 	rule arith(_, #nan, Right:JS) => #nan
--- 	rule arith(_, Left:JS, #nan) => #nan
--- 
--- --- arithmetic with infinity	
--- 	rule arith(`div, #infinity(_), #infinity(_)) => #nan	
--- 	rule arith(`div, Number, #infinity(B)) => getZero(asSignValue(Number), B)
--- 	rule arith(`div, #infinity(A), Number) => getInfinity(A, asSignValue(Number))
--- 
--- 	rule arith(`mod, #infinity(_), _) => #nan
--- 	rule arith(`mod, Number, #infinity(B)) => Number
--- 
--- 	rule arith(`mul, #infinity(A), #infinity(B)) => getInfinity(A, B)
--- 	rule arith(`mul, #zero(_), #infinity(_)) => #nan 
--- 	rule arith(`mul, #infinity(_), #zero(_)) => #nan 
--- 	rule arith(`mul, Number:JS, #infinity(B)) => getInfinity(asSignValue(Number), B)
--- 	rule arith(`mul, #infinity(A), Number:JS) => getInfinity(A, asSignValue(Number))
--- 
--- 	rule arith(`add, #infinity(A), #infinity(B)) => #nan
--- 	rule arith(`add, Number, #infinity(B)) => #infinity(B)
--- 	
--- 	rule arith(`sub, #infinity(A), #infinity(A)) => #nan
--- 	rule arith(`sub, Number, #infinity(B)) => #infinity(-Int(B))
--- 
--- 	rule arith(_, #infinity(A), Number) => #infinity(A)
--- 	
--- --- arithmetic with zero	
--- 	--- CHECK FOR -ZERO in AST from Narcissus parser!!!
--- 	rule arith(`div, #zero(_), #zero(_)) => #nan
--- 	rule arith(`div, #zero(A), Number) => getZero(A, asSignValue(Number))
--- 	rule arith(`div, Number, #zero(B)) => getInfinity(asSignValue(Number), B)
--- 
--- 	rule arith(`mod, #zero(A), _) => #zero(A)
--- 	rule arith(`mod, _, #zero(_)) => #nan
--- 
--- 	macro asSignValue(F:Float) 	= 	if F >=Float 0 then 1 else -1 fi
--- 	macro asSignValue(A:Int) 	= 	if A >=Int 0 then 1 else -1 fi
--- 	
--- 	macro getInfinity(A, B) 	= #infinity(A *Int B)
--- 	macro getZero(A, B) 		= #zero(A *Int B)
--- 	
--- 	macro #n(0) 	= #zero(0)
--- 	macro #n(0.0) 	= #zero(1)
--- 	macro #n(-0.0) 	= #zero(-1)
--- 
--- 	
--- 	rule arith(`div, #n(F1), #n(F2)) => #n(F1 /Float F2)
--- 	rule arith(`mod, #n(F1), #n(F2)) => #n(F1 %Float F2)
--- 	rule arith(`mul, #n(F1), #n(F2)) => #n(F1 *Float F2)
--- 	rule arith(`add, #n(F1), #n(F2)) => #n(F1 +Float F2)
--- 	rule arith(`sub, #n(F1), #n(F2)) => #n(F1 -Float F2)
--- 
--- 	rule arith(`div, #n(I1), #n(I2)) => #n(I1 /Int I2)
--- 	rule arith(`mod, #n(I1), #n(I2)) => #n(I1 %Int I2)
--- 	rule arith(`mul, #n(I1), #n(I2)) => #n(I1 *Int I2)
--- 	rule arith(`add, #n(I1), #n(I2)) => #n(I1 +Int I2)
--- 	rule arith(`sub, #n(I1), #n(I2)) => #n(I1 -Int I2)
--- 
--- 	rule #add(#s(S1:String), #s(S2:String)) => #s(concat(S1, S2))
--- 
--- 	rule #add(#s(S1), Right) => #add(#s(S1), #s(asString(Right))) [structural]
--- 	rule #add(Left, #s(S2)) => #add(#s(asString(Right)), #s(S2)) [structural]
--- 		
--- 	--- rule arith(`add, #s(S1:String), #s(S2:String)) => #s(concat(S1, S2))
--- 
--- 	--- rule arith(`add, #s(S1), Right) => arith(`add, #s(S1), #s(asString(Right))) [structural]
--- 	--- rule arith(`add, Left, #s(S2)) => arith(`add, #s(asString(Right)), #s(S2)) [structural]
--- 	
--- 	rule arith(Op, #n(F1), Right) => arith(Op, #n(F1), #n(asFloat(Right))) [structural]
--- 	rule arith(Op, Left, #n(F2)) => arith(Op, #n(asFloat(Left)), #n(F2)) [structural]
--- 
--- 	rule arith(Op, #n(I1), Right) => arith(Op, #n(I1), #n(asInt(Right))) [structural]
--- 	rule arith(Op, Left, #n(I2)) => arith(Op, #n(asInt(Left)), #n(I2)) [structural]
--- 
--- 
--- 	rule logic(`and, #b(B1), #b(B2)) => #b(B1 &Bool B2)
--- 	rule logic(`or, #b(B1), #b(B2)) => #b(B1 |Bool B2)
--- 
--- 	rule logic(Op, #b(B1), Right) => logic(Op, #b(B1), #b(asBool(Right))) [structural]
--- 	rule logic(Op, Left, #b(B2)) => logic(Op, #b(asBool(Left)), #b(B2)) [structural]
--- 	
--- ---	macro #inc(#n(F1), true) => 
--- ---	macro #dec(#n(F1), true) => 
--- 	
--- 	rule #neg(#n(F1)) => #n(-Float(F1))
--- 	rule #neg(#n(I1)) => #n(-Int(I1))
--- 	rule #neg(Other) => #neg(#n(asNumber(Other))) [structural]
--- 	rule #plus(#n(Num)) => #n(Num)
--- 	rule #plus(Other) => #n(asNumber(Other)) [structural]
--- 	
--- 	rule #not(#b(B1)) => #b(~Bool(B1))
--- 	rule #not(Other) => #not(#b(asBool(Other))) [structural]
--- 	
--- 
--- 	--- | #sameAs ( JS , JS ) [strict] 		--- Exp == Exp
--- 	--- | #notSameAs ( JS , JS ) [strict] 		--- Exp != Exp
--- 	--- | #identical ( JS , JS ) [strict] 		--- Exp === Exp
--- 	--- | #notIdentical ( JS , JS ) [strict] 	--- Exp !== Exp
--- 
---   --- rule V1:Val == V2:Val => V1 ==Bool V2 
---   --- rule V1 != V2 => V1 =/=Bool V2 
---   --- rule T1:Bool and T2:Bool => T1 andBool T2 
---   --- rule T1 or T2 => T1 orBool T2 
---   --- rule not(T:Bool) => notBool(T) 
--- 
--- 
--- 
--- endkm
