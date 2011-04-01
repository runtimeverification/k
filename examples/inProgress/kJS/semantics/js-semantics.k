kmod JS-CONVERSIONS is including JS-SYNTAX + K
	
	syntax K ::= toPrimitive( K , String ) 
		| toBoolean( JSValue ) | toNumber( JSValue ) | toString( JSValue )
	
	--- ECMA-262 9.1
---	macro toPrimitive(Prim:JSPrimitive, Hint:List{K}) 	= Prim 
---	macro toPrimitive(Value:JSValue) 				= toPrimitive(Value, $s("number")) 
	rule toPrimitive(Value:JSValue, "N")	=> toNumber(Value)
	rule toPrimitive(Value, "S") 			=> toString(Value)
	
	--- ECMA-262 9.2
	rule toBoolean(Value) 	=> $b(isTruthy(Value))

	syntax Bool ::= isTruthy( JSValue )
	
	rule isTruthy($undefined) 		=> false
	rule isTruthy($null) 			=> false
	rule isTruthy($b(B:Bool)) 		=> B
	rule isTruthy($zero(I:Int)) 	=> false
	rule isTruthy($nan) 			=> false
	rule isTruthy($s("")) 			=> false
	rule isTruthy($o(Value)) 		=> true
	
	--- ECMA-262 9.3
	rule toNumber(Numeric:JSNumeric)	=> Numeric
	rule toNumber($undefined) 			=> $nan
	rule toNumber($null) 				=> $n(0)
	rule toNumber($b(true)) 			=> $n(1)
	rule toNumber($b(false)) 			=> $n(0)
	rule toNumber($s(""))				=> $n(0)
	rule toNumber($s(S:String))			=> $n(String2Float(S))
	rule toNumber(Obj:JSObject)			=> $nan
	--- NOTE: some objects (such as arrays) map to $n(0)  !!!
	
	--- ECMA-262 9.8
	rule toString($undefined) 	=> $s("undefined")
	rule toString($null) 		=> $s("null")
	rule toString($b(true)) 	=> $s("true")
	rule toString($b(false)) 	=> $s("false")
	rule toString($nan) 		=> $s("NaN")
	rule toString($n(I:Int)) 	=> $s(Int2String(I))
	rule toString($n(F:Float)) 	=> $s(Float2String(F))
	rule toString($infinity(1)) => $s("Infinity")
	rule toString($infinity(-1)) => $s("-Infinity")
	rule toString($zero(I)) 	=> $s("0")
	rule toString($s(S)) 		=> $s(S)
	rule toString(Obj:JSObject) => $s("[object Object]")
	---	rule toString($s(S)) 		=> #invocation(#staticAccess(newString(S),$s("toString")),#comma(.List{JS}))	
endkm 

kmod JS-TYPEOF is including JS-SYNTAX + K

	--- ECMA-262 11.4.3
	rule #typeof($undefined) 		=> $s("undefined")
	rule #typeof($null) 			=> $s("object")
	rule #typeof($b(B:Bool)) 		=> $s("boolean")
	rule #typeof(Numeric:JSNumeric) => $s("number")
	rule #typeof($s(S:String)) 		=> $s("string")
	rule #typeof($o(Value:JSValue)) => $s("object")
	--- rule #typeof($function(_, _, _, _))	=> $s("function")	
endkm

kmod JS-UNARY is including JS-CONVERSIONS + PL-BOOL 
	
	--- ECMA-262 11.4.6
	rule #plus(Value) => toNumber(Value)

	--- ECMA-262 11.4.7
	rule #neg(Value) => neg(Value)

	syntax JSNumeric ::= neg ( JSValue )
	
	rule neg($n(F:Float)) 	=> $n(-Float(F))
	rule neg($n(I:Int)) 	=> $n(-Int(I))
	rule neg($zero(F)) 		=> $zero(-Float(F))
	rule neg($infinity(F)) 	=> $infinity(-Float(F))
	rule neg($nan) 			=> $nan
	rule neg(Value:JSValue) => neg(toNumber(Value))

	--- ECMA-262 11.4.8
	rule #not($b(B:Bool)) 	=> not($b(B))
	rule #not(Value) 		=> not(toBoolean(Value))

	syntax JSBoolean ::= not ( JSBoolean )
	
	rule not($b(B)) 		=> $b(notBool(B))

	
	---	macro #inc($n(F1), true) => 
	---	macro #dec($n(F1), true) => 
	
endkm

kmod JS-ARITHMETIC is including JS-UNARY + JS-SYNTAX 

	syntax K ::= arith( String , K , K ) 
				| getInfinity( Int , Int ) 
				| getZero( Int , Int )
			
	rule getInfinity(Sign1:Int, Sign2:Int) 	=> $infinity(Sign1 *Int Sign2)
	rule getZero(Sign1, Sign2) 				=> $zero(Sign1 *Int Sign2)
	
	--- arithmetic expressions
	rule #div(Left:K, Right:K) 	=> arith("div", Left, Right)
	rule #mod(Left, Right) 		=> arith("mod", Left, Right)
	rule #mul(Left, Right) 		=> arith("mul", Left, Right)
	rule #sub(Left, Right) 		=> arith("sub", Left, Right)
	rule #add(Left, Right) 		=> arith("add", toPrimitive(Left, "N"), toPrimitive(Right, "N"))
	
	--- arithmetic base cases
	rule arith("div", $n(F1:Float), $n(F2:Float)) 	=> $n(F1 /Float F2)
	rule arith("mod", $n(F1), $n(F2)) 				=> $n(F1 %Float F2)
	rule arith("mul", $n(F1), $n(F2)) 				=> $n(F1 *Float F2)
	rule arith("add", $n(F1), $n(F2)) 				=> $n(F1 +Float F2)
	rule arith("sub", $n(F1), $n(F2)) 				=> $n(_-Float_(F1, F2))

	rule arith("div", $n(I1:Int), $n(I2:Int)) 		=> $n(I1 /Int I2)
	rule arith("mod", $n(I1), $n(I2)) 				=> $n(I1 %Int I2)
	rule arith("mul", $n(I1), $n(I2)) 				=> $n(I1 *Int I2)
	rule arith("add", $n(I1), $n(I2)) 				=> $n(I1 +Int I2)
	rule arith("sub", $n(I1), $n(I2)) 				=> $n(_-Int_(I1, I2))
	
	--- arithmetic with NaN
	rule arith(OpId:String, $nan, Right) 	=> $nan
	rule arith(OpId, Left, $nan) 			=> $nan


	--- ECMA-262 11.5.1
	rule arith("mul", $infinity(Sign1), $infinity(Sign2)) 	=> getInfinity(Sign1, Sign2)
	rule arith("mul", $zero(Sign1), $infinity(Sign2)) 		=> $nan 
	rule arith("mul", $infinity(Sign1), $zero(Sign2)) 		=> $nan 
	rule arith("mul", $zero(Sign1), Num:JSNumber) 			=> getZero(Sign1, sign(Num))
	rule arith("mul", Num, $zero(Sign2)) 					=> getZero(sign(Num), Sign2)
	rule arith("mul", $infinity(Sign1), Num) 				=> getInfinity(Sign1, sign(Num))
	rule arith("mul", Num, $infinity(Sign2)) 				=> getInfinity(sign(Num), Sign2)
	
	--- ECMA-262 11.5.2
	rule arith("div", $infinity(Sign1), $infinity(Sign2)) 	=> $nan	
	rule arith("div", $infinity(Sign1), Num) 				=> getInfinity(Sign1, sign(Num))
	rule arith("div", Num, $infinity(Sign2)) 				=> getZero(sign(Num), Sign2)
	rule arith("div", $zero(Sign1), $zero(Sign2)) 			=> $nan
	rule arith("div", $zero(Sign1), Num) 					=> getZero(Sign1, sign(Num))
	rule arith("div", Num, $zero(Sign2)) 					=> getInfinity(sign(Num), Sign2)
	
	--- ECMA-262 11.5.3
	rule arith("mod", $infinity(Sign1), Num) 	=> $nan
	rule arith("mod", Num, $zero(Sign2)) 		=> $nan
	rule arith("mod", Num, $infinity(Sign2)) 	=> Num
	rule arith("mod", $zero(Sign1), Num) 		=> $zero(Sign1)
	
	--- ECMA-262 11.6.1
	rule arith("add", $s(S1:String), $s(S2:String)) => $s(_+String_(S1, S2))
	rule arith("add", $s(S1), Value:JSValue) 		=> arith("add", $s(S1), toString(Value))
	rule arith("add", Value, $s(S2)) 				=> arith("add", toString(Value), $s(S2))

	rule arith("add", $infinity(Sign1), $infinity(Sign2)) 	=> $nan
	rule arith("add", Num, $infinity(Sign2)) 				=> $infinity(Sign2)
	rule arith("add", $infinity(Sign1), Num) 				=> $infinity(Sign1)
	rule arith("add", $zero(Sign1), $zero(Sign2)) 			=> $zero(1)
	rule arith("add", $zero(Sign1), Num) 					=> Num
	rule arith("add", Num, $zero(Sign2)) 					=> Num
	
	--- ECMA-262 11.6.3
	rule arith("sub", Left, Right) => arith("add", Left, neg(Right))
	
	--- arithmetic conversions	
	rule arith(OpId, Left, Right) => arith(OpId, toNumber(Left), toNumber(Right))
	
endkm

kmod JS-COMPARISON is including JS-UNARY + JS-SYNTAX + PL-BUILTINS

	--- ECMA-262 11.8.1-4
	rule #lt(Left:K, Right:K) 	=> comparison(lessThan(Left, Right), true)
	rule #gt(Left:K, Right:K) 	=> comparison(lessThan(Right, Left), true)
	rule #lte(Left:K, Right:K) 	=> comparison(lessThan(Right, Left), false)
	rule #lte(Left:K, Right:K) 	=> comparison(lessThan(Left, Right), false)

	--- ECMA-262 11.8.5
	
	syntax JSBoolean ::= comparison( JSPrimitive , Bool )
	syntax JSPrimitive ::= lessThan( JSPrimitive , JSPrimitive )
	
	rule comparison($undefined, B:Bool)	=> $b(false)
	rule comparison($b(B:Bool), true)	=> $b(B)
	rule comparison($b(B:Bool), false)	=> not($b(B))
	
	rule lessThan($nan, Right)					=> $undefined
	rule lessThan(Left, $nan)					=> $undefined
	rule lessThan($s(S1:String), $s(S2:String)) => $b(_<String_(S1, S2))
	rule lessThan($n(I1:Int), $n(I2:Int)) 	 	=> $b(_<Int_(I1, I2))
	rule lessThan(N1:JSNumeric, N2:JSNumeric) 	=> $b(_<Float_(numericValue(N1), numericValue(N2)))
	rule lessThan(Left, Right) 				 	=> lessThan(toNumber(Left), toNumber(Right))	
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
--- 	macro equal(N1, O2:JSObject)			= #equal(N1, toPrimitive(O2, "N"))
--- 	macro equal(O1:JSObject, N2)			= #equal(toPrimitive(O1, "N"), N2)
--- 	macro equal(S1, O2)						= #equal(S1, toPrimitive(O2, "N"))
--- 	macro equal(O1, S2)						= #equal(toPrimitive(O1, "N"), S2)
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