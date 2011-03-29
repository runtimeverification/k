load ../syntax/js-syntax.k

kmod JS-CONVERSIONS
	is protecting JS-SYNTAX + PL-BUILTINS .
	
	syntax JS ::= toFloat( JS ) | toInt( JS ) | toBoolean( JS ) | toString( JS )
	
	--- ECMA-262 9.1
	macro toPrimitive(Prim:JSPrimitive, .List{JS}) 	= Prim 
	macro toPrimitive(Value:JS) 					= toPrimitive(Value:JS, "number") 
	macro toPrimitive(Value, "number") 				= toNumber(Value)
	macro toPrimitive(Value, "string") 				= toString(Value)
	
	--- ECMA-262 9.2
	macro toBoolean($undefined) 	= $b(false)
	macro toBoolean($null) 			= $b(false)
	macro toBoolean($b(B:Bool)) 	= $b(B)
	macro toBoolean($zero(_)) 		= $b(false)
	macro toBoolean($nan) 			= $b(false)
	macro toBoolean($s("")) 		= $b(false)
	macro toBoolean(_) 				= $b(true)

	--- ECMA-262 9.3
	macro toNumber(Numeric:JSNumeric)	= Numeric
	macro toNumber(Value:JS)			= toFloat(Value)

	macro toFloat($s(S:String))			= $n(String2Float(S))
	macro toFloat($n(F:Float))			= $n(F)
	macro toFloat($n(I:Int)) 			= $n(Int2Float(I))
	macro toFloat(Value) 				= toInt(Value)
	
	macro toInt($s(S:String)) 			= $n(String2Int(S))
	macro toInt($undefined) 			= $nan
	macro toInt($null) 					= $n(0)
	macro toInt($b(true)) 				= $n(1)
	macro toInt($b(false)) 				= $n(0)
	macro toInt($n(F:Float)) 			= $n(Float2Int(F))
	macro toInt(Num:JSNumber) 			= Num
	macro toInt(_)						= $nan
	--- NOTE: some objects (such as arrays) map to $n(0)  !!!
	
	--- ECMA-262 9.8
	macro toString($undefined) 			= $s("undefined")
	macro toString($null) 				= $s("null")
	macro toString($b(true)) 			= $s("true")
	macro toString($b(false)) 			= $s("false")
	macro toString($nan) 				= $s("NaN")
	macro toString($n(I:Int)) 			= $s(Int2String(I))
	macro toString($n(F:Float)) 		= $s(Float2String(F))
	macro toString($infinity(F)) 		= $s(Float2String(F))
	---macro toString($infinity(I)) = if I >=Int 0 then $s("Infinity") else $s("-Infinity") fi
	macro toString($zero(_)) 			= $s("0")
	macro toString($s(S)) 				= $s(S)
	macro toString(_) 					= $s("[object Object]")
	---	macro toString($s(S)) 		= #invocation(#staticAccess(newString(S),$s("toString")),#comma(.List{JS}))	
endkm 

kmod JS-TYPEOF 
	is protecting JS-SYNTAX .

	--- ECMA-262 11.4.3
	macro #typeof($undefined) 				= $s("undefined")
	macro #typeof($null) 					= $s("object")
	macro #typeof($b(_)) 					= $s("boolean")
	macro #typeof(Numeric:JSNumeric) 		= $s("number")
	macro #typeof($s(_)) 					= $s("string")
	macro #typeof(#o(_)) 					= $s("object")
	macro #typeof(#function(_, _, _, _))	= $s("function")

	--- rule #typeof($undefined) 			=> $s("undefined") [structural]
	--- rule #typeof($null) 				=> $s("object") [structural]
	--- rule #typeof($b(_)) 				=> $s("boolean") [structural]
	--- rule #typeof(Num:JSNumeric) 		=> $s("number") [structural]
	--- rule #typeof($s(_)) 				=> $s("string") [structural]
	--- rule #typeof(#function(_, _, _, _))	=> $s("function") [structural]
	--- rule #typeof(#o(_)) 				=> $s("object") [structural]
	
endkm	

kmod JS-ARITHMETIC
	is protecting JS-SYNTAX + JS-CONVERSIONS + PL-BUILTINS .

	syntax JS ::= arith( String , JS , JS ) 
				| getInfinity( Int , Int ) 
				| getZero( Int , Int )
	
	syntax Int ::= sign( JS )
	
	maude numericValue($n(F:Float))			= F
	maude numericValue($n(I:Int))			= Int2Float(I)
	maude numericValue($zero(_))			= 0.0
	maude numericValue($infinity(I:Int))	= if I >=Int 0 then Infinity else -Infinity fi
	
	
	macro sign(F:Float)			= 	if F >=Float 0.0 then 1 else -1 fi
	macro sign($zero(I)) 		= 	I
	macro sign($infinity(I)) 	= 	I
	macro sign(Num) 			= 	sign(numericValue(Num))
	
	macro getInfinity(Sign1:Int, Sign2:Int) 	= $infinity(Sign1 *Int Sign2)
	macro getZero(Sign1, Sign2) 				= $zero(Sign1 *Int Sign2)

	macro $n(0) 	= $zero(1)
	macro $n(0.0) 	= $zero(1)
---	macro $n(-0.0) 	= $zero(-1)

--- arithmetic expressions
	
	--- ECMA-262 11.4.6
	macro #plus(Value) = toNumber(Value)
	
	--- ECMA-262 11.4.7
	macro neg($n(F)) = $n(-Float(F))
	macro neg($n(I)) = $n(-Int(I))
	macro neg($zero(F)) = $zero(-Float(F))
	macro neg($infinity(F)) = $zero(-Float(F))
	macro neg($nan) = $nan
	macro neg(Value) = neg(toNumber(Value))

	macro #neg(Value) = neg(Value)
	
	macro #div(Left:JS, Right:JS) 	= arith("div", Left, Right)
	macro #mod(Left, Right) 		= arith("mod", Left, Right)
	macro #mul(Left, Right) 		= arith("mul", Left, Right)
	macro #sub(Left, Right) 		= arith("sub", Left, Right)
	macro #add(Left, Right) 		= arith("add", toPrimitive(Left), toPrimitive(Right))
		
	
		--- arithmetic base cases
	macro arith("div", $n(F1), $n(F2)) = $n(F1 /Float F2)
	macro arith("mod", $n(F1), $n(F2)) = $n(F1 %Float F2)
	macro arith("mul", $n(F1), $n(F2)) = $n(F1 *Float F2)
	macro arith("add", $n(F1), $n(F2)) = $n(F1 +Float F2)
	macro arith("sub", $n(F1), $n(F2)) = $n(_-Float_(F1, F2))

	macro arith("div", $n(I1:Int), $n(I2:Int)) = $n(I1 /Int I2)
	macro arith("mod", $n(I1), $n(I2)) = $n(I1 %Int I2)
	macro arith("mul", $n(I1), $n(I2)) = $n(I1 *Int I2)
	macro arith("add", $n(I1), $n(I2)) = $n(I1 +Int I2)
	macro arith("sub", $n(I1), $n(I2)) = $n(_-Int_(I1, I2))

	--- arithmetic with NaN
	macro arith(OpId:String, $nan, Right:JS) = $nan
	macro arith(OpId, Left:JS, $nan) = $nan


	--- ECMA-262 11.5.1
	macro arith("mul", $infinity(Sign1), $infinity(Sign2)) = getInfinity(Sign1, Sign2)
	macro arith("mul", $zero(_), $infinity(_)) = $nan 
	macro arith("mul", $infinity(_), $zero(_)) = $nan 
	macro arith("mul", $zero(Sign1), Num) = getZero(Sign1, sign(Num))
	macro arith("mul", Num, $zero(Sign2)) = getZero(sign(Num), Sign2)
	macro arith("mul", $infinity(Sign1), Num) = getInfinity(Sign1, sign(Num))
	macro arith("mul", Num, $infinity(Sign2)) = getInfinity(sign(Num), Sign2)

	--- ECMA-262 11.5.2
	macro arith("div", $infinity(_), $infinity(_)) = $nan	
	macro arith("div", $infinity(Sign1), Num) = getInfinity(Sign1, sign(Num))
	macro arith("div", Num:JSNumber, $infinity(Sign2)) = getZero(sign(Num), Sign2)
	macro arith("div", $zero(_), $zero(_)) = $nan
	macro arith("div", $zero(Sign1), Num) = getZero(Sign1, sign(Num))
	macro arith("div", Num, $zero(Sign2)) = getInfinity(sign(Num), Sign2)

	--- ECMA-262 11.5.3
	macro arith("mod", $infinity(_), _) = $nan
	macro arith("mod", _, $zero(_)) = $nan
	macro arith("mod", Num, $infinity(Sign2)) = Num
	macro arith("mod", $zero(Sign1), _) = $zero(Sign1)

	--- ECMA-262 11.6.1
	macro arith("add", $s(S1:String), $s(S2:String)) = $s(_+String_(S1, S2))
	macro arith("add", $s(S1), Right) 	= arith("add", $s(S1), toString(Right))
	macro arith("add", Left, $s(S2)) 	= arith("add", toString(Left), $s(S2))

	macro arith("add", $infinity(Sign1), $infinity(Sign2)) = $nan
	macro arith("add", Num, $infinity(Sign2)) = $infinity(Sign2)
	macro arith("add", $infinity(Sign1), Num) = $infinity(Sign1)
	macro arith("add", $zero(Sign1), $zero(Sign2)) = $zero(1)
	macro arith("add", $zero(Sign1), Num) = Num
	macro arith("add", Num, $zero(Sign2)) = Num
	
	--- ECMA-262 11.6.3
	macro arith("sub", Left, Right) = arith("add", Left, neg(Right))
	
	
	--- arithmetic conversions
	macro arith(OpId, $n(F1), Right) 	= arith(OpId, $n(F1), toFloat(Right))
	macro arith(OpId, Left, $n(F2)) 	= arith(OpId, toFloat(Left), $n(F2))

	macro arith(OpId, $n(I1), Right) 	= arith(OpId, $n(I1), toInt(Right))
	macro arith(OpId, Left, $n(I2)) 	= arith(OpId, toInt(Left), $n(I2))
	
	macro arith(OpId, Left, Right) 		= arith(OpId, toNumber(Left), toNumber(Right))
	
	---	macro #inc($n(F1), true) => 
	---	macro #dec($n(F1), true) => 
endkm

kmod JS-COMPARISON
	is protecting JS-SYNTAX + JS-CONVERSIONS .

	macro #lt(Left:JS, Right:JS) 	= compare(toPrimitive(Left), toPrimitive(Right), true)
	macro #gt(Left:JS, Right:JS) 	= compare(toPrimitive(Right), toPrimitive(Left), true)
	macro #lte(Left:JS, Right:JS) 	= compare(toPrimitive(Right), toPrimitive(Left), false)
	macro #lte(Left:JS, Right:JS) 	= compare(toPrimitive(Left), toPrimitive(Right), false)
	
	macro islessThan($n(I1:Int), $n(I2:Int)) 		= $b(<Int(I1, I2))
	macro islessThan($n(F1:Float), $n(F2:Float)) 	= $b(<Float(F1, F2))
	macro islessThan(N1, N2) 				= islessThan(numericValue(N1), numericValue(N2)))
	
	macro compare($nan, _, _)						= $b(false)
	macro compare(_, $nan, _)						= $b(false)
	macro compare(N1:JSNumeric, N2:JSNumeric, true)	= islessThan(N1, N2)
	macro compare(N1, N2, false)					= not(islessThan(N1, N2))
	
endkm

kmod JS-IDENTITY
	is protecting JS-SYNTAX + JS-CONVERSIONS .

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

	macro #identical($nan, $nan)				= $b(false)
	macro #identical(V1, V1) 					= $b(true)
	
	macro #identical($null, $undefined)			= $b(true)
	macro #identical($undefined, $null)			= $b(true)
	macro #identical($zero(_), $zero(_))		= $b(true)
	macro #identical($n(F:Float), $n(I:Int)) 	= #identical($n(F), toFloat($n(I)))
	macro #identical($n(I), $n(F)) 				= #identical(toFloat($n(I)), $n(F))
	
	macro #identical(Left:JS, Right:JS) 		= $b(false)

	macro #notIdentical(Left, Right) 			= not(#identical(Left, Right))	
endkm



kmod JS-LOGIC
	is protecting JS-SYNTAX + JS-CONVERSIONS + PL-BUILTINS .

	syntax JS ::= logic( String , JS , JS )

	macro not($b(B1)) 								= $b(notBool(B1))
	macro #not(B1) 									= not(B1)
	macro #not(Value:JS) 							= not(toBoolean(Other))
	
	macro #and(Left:JS, Right:JS) 					= logic("and", Left, Right)
	macro #or(Left, Right)  						= logic("or", Left, Right)
	
	macro logic("and", $b(B1:Bool), $b(B2:Bool)) 	= $b(B1 andBool B2)
	macro logic("or", $b(B1), $b(B2)) 				= $b(B1 orBool B2)

	macro logic(OpId:String, $b(B1), Right) 		= logic(OpId, $b(B1), toBoolean(Right))
	macro logic(OpId, Left, $b(B2)) 				= logic(OpId, toBoolean(Left), $b(B2))
endkm
	

kmod JS-SEMANTICS
	is including 
	  JS-CONVERSIONS 
	+ JS-TYPEOF
	+ JS-IDENTITY
	+ JS-ARITHMETIC
	+ JS-LOGIC
endkm
