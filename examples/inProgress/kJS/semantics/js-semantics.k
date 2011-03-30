kmod JS-CONVERSIONS is including JS-SYNTAX
	
	syntax JS ::= toPrimitive( List{JS} ) 
		| toBoolean( JSValue ) | toNumber( JSValue ) | toString( JSValue )
	
	--- ECMA-262 9.1
	macro toPrimitive(Prim:JSPrimitive, .List{JS}) 	= Prim 
	macro toPrimitive(Value:JSValue) 				= toPrimitive(Value, $s("number")) 
	macro toPrimitive(Value, $s("number"))			= toNumber(Value)
	macro toPrimitive(Value, $s("string")) 			= toString(Value)
	
	--- ECMA-262 9.2
	macro toBoolean(Value) 	= $b(isTruthy(Value))

	syntax Bool ::= isTruthy( JSValue )
	
	macro isTruthy($undefined) 		= false
	macro isTruthy($null) 			= false
	macro isTruthy($b(B:Bool)) 		= B
	macro isTruthy($zero(I:Int)) 	= false
	macro isTruthy($nan) 			= false
	macro isTruthy($s("")) 			= false
	macro isTruthy($o(Value)) 		= true
	
	--- ECMA-262 9.3
	macro toNumber(Numeric:JSNumeric)	= Numeric
	macro toNumber($undefined) 			= $nan
	macro toNumber($null) 				= $n(0)
	macro toNumber($b(true)) 			= $n(1)
	macro toNumber($b(false)) 			= $n(0)
	macro toNumber($s(""))				= $n(0)
	macro toNumber($s(S:String))		= $n(String2Float(S))
	macro toNumber(Obj:JSObject)		= $nan
	--- NOTE: some objects (such as arrays) map to $n(0)  !!!
	
	--- ECMA-262 9.8
	macro toString($undefined) 			= $s("undefined")
	macro toString($null) 				= $s("null")
	macro toString($b(true)) 			= $s("true")
	macro toString($b(false)) 			= $s("false")
	macro toString($nan) 				= $s("NaN")
	macro toString($n(I:Int)) 			= $s(Int2String(I))
	macro toString($n(F:Float)) 		= $s(Float2String(F))
	macro toString($infinity(1)) 		= $s("Infinity")
	macro toString($infinity(-1)) 		= $s("-Infinity")
	macro toString($zero(I)) 			= $s("0")
	macro toString($s(S)) 				= $s(S)
	macro toString(Obj:JSObject) 		= $s("[object Object]")
	---	macro toString($s(S)) 		= #invocation(#staticAccess(newString(S),$s("toString")),#comma(.List{JS}))	
endkm 

kmod JS-TYPEOF is including JS-SYNTAX 

	--- ECMA-262 11.4.3
	macro #typeof($undefined) 				= $s("undefined")
	macro #typeof($null) 					= $s("object")
	macro #typeof($b(B:Bool)) 				= $s("boolean")
	macro #typeof(Numeric:JSNumeric) 		= $s("number")
	macro #typeof($s(S:String)) 			= $s("string")
	macro #typeof($o(Value:JSValue)) 		= $s("object")
	--- macro #typeof($function(_, _, _, _))	= $s("function")

	--- rule #typeof($undefined) 			=> $s("undefined") [structural]
	--- rule #typeof($null) 				=> $s("object") [structural]
	--- rule #typeof($b(_)) 				=> $s("boolean") [structural]
	--- rule #typeof(Num:JSNumeric) 		=> $s("number") [structural]
	--- rule #typeof($s(_)) 				=> $s("string") [structural]
	--- rule #typeof(#function(_, _, _, _))	=> $s("function") [structural]
	--- rule #typeof(#o(_)) 				=> $s("object") [structural]
	
endkm

kmod JS-UNARY is including JS-CONVERSIONS + PL-BOOL 
	
	--- ECMA-262 11.4.6
	macro #plus(Value) = toNumber(Value)

	--- ECMA-262 11.4.7
	macro #neg(Value) = neg(Value)

	syntax JSNumeric ::= neg ( JSValue )
	
	macro neg($n(F:Float)) 		= $n(-Float(F))
	macro neg($n(I:Int)) 		= $n(-Int(I))
	macro neg($zero(F)) 		= $zero(-Float(F))
	macro neg($infinity(F)) 	= $infinity(-Float(F))
	macro neg($nan) 			= $nan
	macro neg(Value:JSValue) 	= neg(toNumber(Value))

	--- ECMA-262 11.4.8
	macro #not($b(B:Bool)) 		= not($b(B))
	macro #not(Value) 			= not(toBoolean(Value))

	syntax JSBoolean ::= not ( JSBoolean )
	
	macro not($b(B)) 			= $b(notBool(B))

	
	---	macro #inc($n(F1), true) => 
	---	macro #dec($n(F1), true) => 
	
endkm

kmod JS-ARITHMETIC is including JS-UNARY + JS-SYNTAX 

	syntax JS ::= arith( String , JS , JS ) 
				| getInfinity( Int , Int ) 
				| getZero( Int , Int )
			
	macro getInfinity(Sign1:Int, Sign2:Int) 	= $infinity(Sign1 *Int Sign2)
	macro getZero(Sign1, Sign2) 				= $zero(Sign1 *Int Sign2)
	
	--- arithmetic expressions
	macro #div(Left:JS, Right:JS) 	= arith("div", Left, Right)
	macro #mod(Left, Right) 		= arith("mod", Left, Right)
	macro #mul(Left, Right) 		= arith("mul", Left, Right)
	macro #sub(Left, Right) 		= arith("sub", Left, Right)
	macro #add(Left, Right) 		= arith("add", toPrimitive(Left), toPrimitive(Right))
	
	--- arithmetic base cases
	macro arith("div", $n(F1:Float), $n(F2:Float)) 	= $n(F1 /Float F2)
	macro arith("mod", $n(F1), $n(F2)) 				= $n(F1 %Float F2)
	macro arith("mul", $n(F1), $n(F2)) 				= $n(F1 *Float F2)
	macro arith("add", $n(F1), $n(F2)) 				= $n(F1 +Float F2)
	macro arith("sub", $n(F1), $n(F2)) 				= $n(_-Float_(F1, F2))

	macro arith("div", $n(I1:Int), $n(I2:Int)) 		= $n(I1 /Int I2)
	macro arith("mod", $n(I1), $n(I2)) 				= $n(I1 %Int I2)
	macro arith("mul", $n(I1), $n(I2)) 				= $n(I1 *Int I2)
	macro arith("add", $n(I1), $n(I2)) 				= $n(I1 +Int I2)
	macro arith("sub", $n(I1), $n(I2)) 				= $n(_-Int_(I1, I2))
	
	--- arithmetic with NaN
	macro arith(OpId:String, $nan, Right) 	= $nan
	macro arith(OpId, Left, $nan) 			= $nan


	--- ECMA-262 11.5.1
	macro arith("mul", $infinity(Sign1), $infinity(Sign2)) 	= getInfinity(Sign1, Sign2)
	macro arith("mul", $zero(Sign1), $infinity(Sign2)) 		= $nan 
	macro arith("mul", $infinity(Sign1), $zero(Sign2)) 		= $nan 
	macro arith("mul", $zero(Sign1), Num:JSNumber) 			= getZero(Sign1, sign(Num))
	macro arith("mul", Num, $zero(Sign2)) 					= getZero(sign(Num), Sign2)
	macro arith("mul", $infinity(Sign1), Num) 				= getInfinity(Sign1, sign(Num))
	macro arith("mul", Num, $infinity(Sign2)) 				= getInfinity(sign(Num), Sign2)
	
	--- ECMA-262 11.5.2
	macro arith("div", $infinity(Sign1), $infinity(Sign2)) 	= $nan	
	macro arith("div", $infinity(Sign1), Num) 				= getInfinity(Sign1, sign(Num))
	macro arith("div", Num, $infinity(Sign2)) 				= getZero(sign(Num), Sign2)
	macro arith("div", $zero(Sign1), $zero(Sign2)) 			= $nan
	macro arith("div", $zero(Sign1), Num) 					= getZero(Sign1, sign(Num))
	macro arith("div", Num, $zero(Sign2)) 					= getInfinity(sign(Num), Sign2)
	
	--- ECMA-262 11.5.3
	macro arith("mod", $infinity(Sign1), Num) 	= $nan
	macro arith("mod", Num, $zero(Sign2)) 		= $nan
	macro arith("mod", Num, $infinity(Sign2)) 	= Num
	macro arith("mod", $zero(Sign1), Num) 		= $zero(Sign1)
	
	--- ECMA-262 11.6.1
	macro arith("add", $s(S1:String), $s(S2:String)) 	= $s(_+String_(S1, S2))
	macro arith("add", $s(S1), Value:JSValue) 			= arith("add", $s(S1), toString(Value))
	macro arith("add", Value, $s(S2)) 					= arith("add", toString(Value), $s(S2))

	macro arith("add", $infinity(Sign1), $infinity(Sign2)) 	= $nan
	macro arith("add", Num, $infinity(Sign2)) 				= $infinity(Sign2)
	macro arith("add", $infinity(Sign1), Num) 				= $infinity(Sign1)
	macro arith("add", $zero(Sign1), $zero(Sign2)) 			= $zero(1)
	macro arith("add", $zero(Sign1), Num) 					= Num
	macro arith("add", Num, $zero(Sign2)) 					= Num
	
	--- ECMA-262 11.6.3
	macro arith("sub", Left, Right) = arith("add", Left, neg(Right))
	
	--- arithmetic conversions	
	macro arith(OpId, Left, Right) 	= arith(OpId, toNumber(Left), toNumber(Right))
	
endkm

kmod JS-COMPARISON is including JS-UNARY + JS-SYNTAX + PL-BUILTINS

	--- ECMA-262 11.8.1-4
	macro #lt(Left:JS, Right:JS) 	= comparison(lessThan(Left, Right), true)
	macro #gt(Left:JS, Right:JS) 	= comparison(lessThan(Right, Left), true)
	macro #lte(Left:JS, Right:JS) 	= comparison(lessThan(Right, Left), false)
	macro #lte(Left:JS, Right:JS) 	= comparison(lessThan(Left, Right), false)

	--- ECMA-262 11.8.5
	
	syntax JSBoolean ::= comparison( JSPrimitive , Bool )
	syntax JSPrimitive ::= lessThan( JSPrimitive , JSPrimitive )
	
	macro comparison($undefined, B:Bool)	= $b(false)
	macro comparison($b(B:Bool), true)		= $b(B)
	macro comparison($b(B:Bool), false)		= not($b(B))
	
	macro lessThan($nan, Right)					 = $undefined
	macro lessThan(Left, $nan)					 = $undefined
	macro lessThan($s(S1:String), $s(S2:String)) = $b(_<String_(S1, S2))
	macro lessThan($n(I1:Int), $n(I2:Int)) 	 	 = $b(_<Int_(I1, I2))
	macro lessThan(N1:JSNumeric, N2:JSNumeric) 	 = $b(_<Float_(numericValue(N1), numericValue(N2)))
	macro lessThan(Left, Right) 				 = lessThan(toNumber(Left), toNumber(Right))	
endkm


--- kmod JS-IDENTITY is including JS-UNARY + JS-SYNTAX
--- 	syntax Bool ::= eitherIsNaN( JS , JS )
--- 	syntax JSBool ::= identical( JS , JS )
--- 	
--- 	--- ECMA-262 11.9.4-6
--- 	macro eitherIsNaN($nan, Right)			= false
--- 	macro eitherIsNaN(Left, $nan)			= false
--- 	macro eitherIsNaN(Left:JS, Right:JS)	= true
--- 	
--- 	macro #notIdentical(Left, Right) = not(#identical(Left, Right))
--- 	
--- 	macro #identical(Left, Right) 	 = $b(false) 				if eitherIsNaN(Left, Right)
--- 	macro #identical(Left, Right)	 = identical(Left, Right) 	[owise]
--- 	
--- 	
--- 	macro identical(P1:JSPrimitive, P1) 			= $b(true)
--- 	
--- 	macro identical($zero(I1:Int), $zero(I2:Int))	= $b(true)
--- 	macro identical($n(F1:Float), $n(I2)) 			= identical($n(F1), $n(Int2Float(I2)))
--- 	macro identical($n(I1), $n(F2:Float)) 			= identical($n(Int2Float(I1)), $n(F2))
--- 	--- Add object reference comparison!!!
--- 	macro identical(Left, Right:JS) 				= $b(false)
--- 
--- endkm
--- 
--- kmod JS-EQUALITY is including JS-UNARY + JS-SYNTAX + JS-IDENTITY 
--- 	syntax JSBool ::= equal( JS , JS )
--- 	
--- 	--- ECMA-262 11.9.1-3
--- 	macro #notEqual(V1, V2) 	= not(#equal(V1, V2))
--- 	
--- 	macro #equal(V1:JS, V2:JS)	= $b(false) if eitherIsNaN(V1, V2)
--- 	macro #equal(V1, V2) 		= $b(true)  if identical(V1, V2)
--- 	macro #equal(V1, V2) 		= equal(V1, V2) [owise]
--- 	
--- 	macro equal($null, $undefined)			= $b(true)
--- 	macro equal($undefined, $null)			= $b(true)
--- 	
--- 	macro equal(N1:JSNumeric, S2:String)	= #equal(N1, toNumber(S2))
--- 	macro equal(S1:String, N2:JSNumeric)	= #equal(toNumber(S1), N2)
--- 	macro equal(B1:JSBool, V2)				= #equal(toNumber(B1), V2)
--- 	macro equal(V1, B2:JSBool)				= #equal(V1, toNumber(B2))
--- 	macro equal(N1, O2:JSObject)			= #equal(N1, toPrimitive(O2))
--- 	macro equal(O1:JSObject, N2)			= #equal(toPrimitive(O1), N2)
--- 	macro equal(S1, O2)						= #equal(S1, toPrimitive(O2))
--- 	macro equal(O1, S2)						= #equal(toPrimitive(O1), S2)
--- 	macro equal(V1, V2)						= $b(false)
--- endkm
--- 
--- kmod JS-LOGIC is including JS-SYNTAX + JS-CONVERSIONS
--- 	
--- 	--- ECMA-262 11.11
--- 	macro #and(Value:JSValue, Exp:JS) 	= if isTruthy(Value) then Val else Exp fi
--- 	macro #or(Val, Exp) 				= if isTruthy(Value) then Exp else Val fi
--- endkm


kmod JS-SEMANTICS
	is including 
	  JS-CONVERSIONS 
	+ JS-TYPEOF
	+ JS-UNARY
	+ JS-ARITHMETIC
	+ JS-COMPARISON
	--- + JS-IDENTITY
	--- + JS-EQUALITY
	--- + JS-LOGIC
endkm