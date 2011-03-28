load ../syntax/js-syntax.k

kmod JS-COERCION
	is protecting JS-SYNTAX + PL-BUILTINS .
	
	syntax JS ::= #asFloat( JS ) | #asInt( JS ) | #asBool( JS ) | #asString( JS )
	
	macro #asFloat(#n(F:Float))		= #n(F)
	macro #asFloat(#n(I:Int)) 		= #n(Int2Float(I))
	macro #asFloat(#s(S:String))	= #n(String2Float(S))
	macro #asFloat(Other:JS) 		= #asInt(Other)
	
	macro #asInt(#n(F:Float)) 		= #n(Float2Int(F))
	macro #asInt(#n(I:Int)) 		= #n(I)
	macro #asInt(#s(S:String)) 		= #n(String2Int(S))
	macro #asInt(#b(true)) 			= #n(1)
	macro #asInt(#b(false)) 		= #n(0)
	macro #asInt(#null) 			= #n(0)
	macro #asInt(#undefined) 		= #n(0)
	macro #asInt(_)					= #nan
	
	macro #asBool(#b(B:Bool)) 		= #b(B)
	macro #asBool(#zero(_)) 		= #b(false)
	macro #asBool(#nan) 			= #b(false)
	macro #asBool(#null) 			= #b(false)
	macro #asBool(#undefined) 		= #b(false)
	macro #asBool(#s("")) 			= #b(false)
	macro #asBool(_) 				= #b(true)

	macro #asString(#s(S)) = #s(S)
	macro #asString(#n(F:Float)) = #s(Float2String(F))
	macro #asString(#n(I:Int)) = #s(Int2String(I))
	macro #asString(#infinity(I)) = if I >=Int 0 then #s("Infinity") else #s("-Infinity") fi
	macro #asString(#nan) = #s("NaN")
	macro #asString(#b(true)) = #s("true")
	macro #asString(#b(false)) = #s("false")
	macro #asString(#null) = #s("null")
	macro #asString(#undefined) = #s("undefined")
	macro #asString(_) = #s("[object Object]")
	---	macro #asString(#s(S)) 		= #invocation(#staticAccess(newString(S),#s("toString")),#comma(.List{JS}))	
endkm 

kmod JS-TYPEOF 
	is protecting JS-SYNTAX .

	macro #typeof(#undefined) 			= #s("undefined")
	macro #typeof(#null) 				= #s("object")
	macro #typeof(#b(_)) 				= #s("boolean")
	macro #typeof(Numeric:JSNumeric) 	= #s("number")
	macro #typeof(#s(_)) 				= #s("string")
	macro #typeof(#function(_, _, _, _))	= #s("function")
	macro #typeof(#o(_)) 				= #s("object")

	--- rule #typeof(#undefined) 			=> #s("undefined") [structural]
	--- rule #typeof(#null) 				=> #s("object") [structural]
	--- rule #typeof(#b(_)) 				=> #s("boolean") [structural]
	--- rule #typeof(Num:JSNumeric) 		=> #s("number") [structural]
	--- rule #typeof(#s(_)) 				=> #s("string") [structural]
	--- rule #typeof(#function(_, _, _, _))	=> #s("function") [structural]
	--- rule #typeof(#o(_)) 				=> #s("object") [structural]
	
endkm	

kmod JS-IDENTITY
	is protecting JS-SYNTAX + JS-COERCION .

--- https://developer.mozilla.org/en/JavaScript/Reference/Operators/Comparison_Operators
--- For strict equality the objects being compared must have the same type and:
--- 
---     Two strings are strictly equal when they have the same sequence of characters, same length,
---		 and same characters in corresponding positions.
---     Two numbers are strictly equal when they are numerically equal (have the same number value).
---		 NaN is not equal to anything, including NaN. 
---		 Positive and negative zeros are equal to one another.
---     Two Boolean operands are strictly equal if both are true or both are false.
---     Two objects are strictly equal if they refer to the same Object.
---     Null and Undefined types are == (but not ===).

	macro #identical(#nan, #nan)				= #b(false)
	macro #identical(V1, V1) 					= #b(true)
	
	macro #identical(#null, #undefined)			= #b(true)
	macro #identical(#undefined, #null)			= #b(true)
	macro #identical(#zero(_), #zero(_))		= #b(true)
	macro #identical(#n(F:Float), #n(I:Int)) 	= #identical(#n(F), #asFloat(#n(I)))
	macro #identical(#n(I), #n(F)) 				= #identical(#asFloat(#n(I)), #n(F))
	
	macro #identical(V1:JS, V2:JS) 				= #b(false)

	macro #notIdentical(V1, V2) 				= #neg(#identical(V1, V2))	
endkm

kmod JS-ARITHMETIC
	is protecting JS-SYNTAX + JS-COERCION + PL-BUILTINS .

	syntax JS ::= arith( String , JS , JS ) 
				| #getInfinity( Int , Int ) 
				| #getZero( Int , Int )
	
	syntax Int ::= asSignValue( JS )
	
	macro asSignValue(F:Float) 	= 	if F >=Float 0.0 then 1 else -1 fi
	macro asSignValue(I:Int) 	= 	if I >=Int 0 then 1 else -1 fi

	macro #getInfinity(I1:Int, I2:Int) 	= #infinity(I1 *Int I2)
	macro #getZero(I1, I2) 		= #zero(I1 *Int I2)

	macro #n(0) 	= #zero(0)
	macro #n(0.0) 	= #zero(1)
---	macro #n(-0.0) 	= #zero(-1)
	
	macro #neg(#n(F1)) = #n(-Float(F1))
	macro #neg(#n(I1)) = #n(-Int(I1))
	macro #neg(Other:JS) = #neg(#asFloat(Other))
	macro #plus(Numeric:JSNumeric) = Numeric
	macro #plus(Other) = #asFloat(Other)
	
	macro #div(Left:JS, Right:JS) = arith("div", Left, Right)
	macro #mod(Left, Right) = arith("mod", Left, Right)
	macro #mul(Left, Right) = arith("mul", Left, Right)
	macro #add(Left, Right) = arith("add", Left, Right)
	macro #sub(Left, Right) = arith("sub", Left, Right)
		
	
--- arithmetic expressions
--- arithmetic base cases
	macro arith("div", #n(F1:Float), #n(F2:Float)) = #n(F1 /Float F2)
	macro arith("mod", #n(F1), #n(F2)) = #n(F1 %Float F2)
	macro arith("mul", #n(F1), #n(F2)) = #n(F1 *Float F2)
	macro arith("add", #n(F1), #n(F2)) = #n(F1 +Float F2)
	macro arith("sub", #n(F1), #n(F2)) = #n(_-Float_(F1, F2))

	macro arith("div", #n(I1:Int), #n(I2:Int)) = #n(I1 /Int I2)
	macro arith("mod", #n(I1), #n(I2)) = #n(I1 %Int I2)
	macro arith("mul", #n(I1), #n(I2)) = #n(I1 *Int I2)
	macro arith("add", #n(I1), #n(I2)) = #n(I1 +Int I2)
	macro arith("sub", #n(I1), #n(I2)) = #n(_-Int_(I1, I2))


--- add with strings	
	--- macro #add(#s(S1:String), #s(S2:String)) = #s(_+String_(S1, S2))
	--- 
	--- macro #add(#s(S1), Right) = #add(#s(S1), #asString(Right))
	--- macro #add(Left, #s(S2)) = #add(#asString(Right), #s(S2))
		
	macro arith("add", #s(S1:String), #s(S2:String)) = #s(_+String_(S1, S2))

	macro arith("add", #s(S1), Right) 	= arith("add", #s(S1), #asString(Right))
	macro arith("add", Left, #s(S2)) 	= arith("add", #asString(Left), #s(S2))


--- arithmetic with NaN
	macro arith(OpId:String, #nan, Right:JS) = #nan
	macro arith(OpId, Left:JS, #nan) = #nan

--- arithmetic with infinity	
	macro arith("div", #infinity(_), #infinity(_)) = #nan	
	macro arith("div", Num:JSNumber, #infinity(I2)) = #getZero(asSignValue(Num), I2)
	macro arith("div", #infinity(I1), Num) = #getInfinity(I1, asSignValue(Num))

	macro arith("mod", #infinity(_), _) = #nan
	macro arith("mod", Num, #infinity(I2)) = Num

	macro arith("mul", #infinity(I1), #infinity(I2)) = #getInfinity(I1, I2)
	macro arith("mul", #zero(_), #infinity(_)) = #nan 
	macro arith("mul", #infinity(_), #zero(_)) = #nan 
	macro arith("mul", Num, #infinity(I2)) = #getInfinity(asSignValue(Num), I2)
	macro arith("mul", #infinity(I1), Num) = #getInfinity(I1, asSignValue(Num))

	macro arith("add", #infinity(I1), #infinity(I2)) = #nan
	macro arith("add", Num, #infinity(I2)) = #infinity(I2)
	
	macro arith("sub", #infinity(I1), #infinity(I1)) = #nan
	macro arith("sub", Num, #infinity(I2)) = #infinity(-Int(I2))

	macro arith(OpId, #infinity(I1), Num) = #infinity(I1)
	
--- arithmetic with zero	
	--- CHECK FOR -ZERO in AST from Narcissus parser!!!
	macro arith("div", #zero(_), #zero(_)) = #nan
	macro arith("div", #zero(I1), Num) = #getZero(I1, asSignValue(Num))
	macro arith("div", Num, #zero(I2)) = #getInfinity(asSignValue(Num), I2)

	macro arith("mod", #zero(I1), _) = #zero(I1)
	macro arith("mod", _, #zero(_)) = #nan

--- arithmetic coercions
	macro arith(OpId, #n(F1), Right) 	= arith(OpId, #n(F1), #asFloat(Right))
	macro arith(OpId, Left, #n(F2)) 	= arith(OpId, #asFloat(Left), #n(F2))

	macro arith(OpId, #n(I1), Right) 	= arith(OpId, #n(I1), #asInt(Right))
	macro arith(OpId, Left, #n(I2)) 	= arith(OpId, #asInt(Left), #n(I2))
	
	---	macro #inc(#n(F1), true) => 
	---	macro #dec(#n(F1), true) => 
	
endkm

kmod JS-LOGIC
	is protecting JS-SYNTAX + JS-COERCION + PL-BUILTINS .

	syntax JS ::= logic( String , JS , JS )

	macro #not(#b(B1)) 								= #b(notBool(B1))
	macro #not(Other:JS) 							= #not(#asBool(Other))
	
	macro #and(Left:JS, Right:JS) 					= logic("and", Left, Right)
	macro #or(Left, Right)  						= logic("or", Left, Right)
	
	macro logic("and", #b(B1:Bool), #b(B2:Bool)) 	= #b(B1 andBool B2)
	macro logic("or", #b(B1), #b(B2)) 				= #b(B1 orBool B2)

	macro logic(OpId:String, #b(B1), Right) 		= logic(OpId, #b(B1), #asBool(Right))
	macro logic(OpId, Left, #b(B2)) 				= logic(OpId, #asBool(Left), #b(B2))
endkm
	

kmod JS-SEMANTICS
	is including 
	  JS-COERCION 
	+ JS-TYPEOF
	+ JS-IDENTITY
	+ JS-ARITHMETIC
	+ JS-LOGIC
endkm
