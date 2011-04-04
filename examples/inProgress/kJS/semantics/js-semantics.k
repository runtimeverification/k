kmod JS-TESTING is including JS-SYNTAX
	syntax Bool ::= isTruthy( JSValue ) 
		| isNumeric( JSValue ) | isNumber( JSValue )
		| isNaN( JSValue ) | isEitherNaN( JSValue , JSValue )

	rule isTruthy($undefined) 			=> false		 [structural]
	rule isTruthy($null) 				=> false		 [structural]
	rule isTruthy($b(B:Bool)) 			=> B			 [structural]
	rule isTruthy($zero(I:Int)) 		=> false		 [structural]
	rule isTruthy($n(N:MaudeNumber)) 	=> true			 [structural]
	rule isTruthy($infinity(I)) 		=> true			 [structural]
	rule isTruthy($nan) 				=> false		 [structural]
	rule isTruthy($s(S:String)) 		=> S =/=Bool ""  [structural]
	rule isTruthy(Obj:JSObject) 		=> true			 [structural]

	rule isNumeric(Numeric:JSNumeric)		=> true  [structural]
	rule isNumeric(NonNumeric:JSNonNumeric)	=> false [structural]

	rule isNumber(Num:JSNumber)				=> true  [structural]
	rule isNumber($infinity(I))				=> false [structural]
	rule isNumber($nan)						=> false [structural]
	rule isNumber(NonNumeric:JSNonNumeric)	=> false [structural]
	
	rule isNaN($nan)						=> true  [structural]
	rule isNaN(NonNaN:JSNonNaN)				=> false [structural]
	
	rule isEitherNaN($nan, Value:JSValue)			=> true  [structural]
	rule isEitherNaN(Value, $nan)					=> true  [structural]
	rule isEitherNaN(NN1:JSNonNaN, NN2:JSNonNaN)	=> false [structural]
	
endkm

kmod JS-CONVERSIONS is including JS-TESTING + PL-BUILTINS
	syntax JSPrimitive ::= toPrimitive( K , String ) 
	syntax JSBoolean ::= toBoolean( JSValue )
	syntax JSNumeric ::= toNumeric( JSValue )
	syntax JSString ::= toString( JSValue )
	
	--- ECMA-262 8.12.8
---	rule defaultValue(Obj:JSObject, Hint:String) --- Not yet implemented!!!
	
	--- ECMA-262 9.1
	rule toPrimitive(Prim:JSPrimitive, Hint:String)	=> Prim [structural]
---	rule toPrimitive(Obj:JSObject, Hint)			=> defaultValue(Obj, Hint) [structural]
	
	--- ECMA-262 9.2
	rule toBoolean(Value:JSValue) 		=> $b(isTruthy(Value)) [structural]
	
	--- ECMA-262 9.3
	rule toNumeric(Numeric:JSNumeric)	=> Numeric 	[structural]
	rule toNumeric($undefined) 			=> $nan		[structural]
	rule toNumeric($null) 				=> $n(0)	[structural]
	rule toNumeric($b(true)) 			=> $n(1)	[structural]
	rule toNumeric($b(false)) 			=> $n(0)	[structural]
	rule toNumeric($s("Infinity"))		=> $infinity(1)
	rule toNumeric($s("-Infinity"))		=> $infinity(-1)
	rule toNumeric($s(S:String))			
		=> if S ==Bool "" then $n(0) else $n(String2Float(S)) fi 
	--- need to handle non-numeric strings !!!
	rule toNumeric(Obj:JSObject)			=> toNumeric(toPrimitive(Obj, "N")) [structural]
	--- NOTE: some objects (such as arrays & numbers) map to $n(0) or $n(n)  !!!
	
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

kmod JS-UNARY is including JS-CONVERSIONS + PL-BUILTINS
	
	--- ECMA-262 11.4.6
	rule #plus(Value:JSValue) => toNumeric(Value)

	--- ECMA-262 11.4.7
	rule #neg(Value) => neg(Value)
	
	syntax JSNumeric ::= neg ( JSValue )
	
	rule neg($n(F:Float)) 	=> $n(-Float(F))						[structural]
	rule neg($n(I:Int)) 	=> $n(-Int(I))							[structural]
	rule neg($zero(I)) 		=> $zero(-Int(I))						[structural]
	rule neg($infinity(I)) 	=> $infinity(-Int(I))					[structural]
	rule neg($nan) 			=> $nan									[structural]
	rule neg(NonNumeric:JSNonNumeric) => neg(toNumeric(NonNumeric))	[structural]
	

	--- ECMA-262 11.4.8
	rule #not(Value) 		=> not(toBoolean(Value))

	syntax JSBoolean ::= not ( JSBoolean )
	
	rule not($b(B:Bool)) 	=> $b(notBool(B))		[structural]

	
	---	macro #inc($n(F1), true) => 
	---	macro #dec($n(F1), true) => 
	
endkm

kmod JS-ARITHMETIC is including JS-UNARY + JS-SYNTAX 

	syntax JSNumeric ::= arith( String , JSValue , JSValue ) 
		| getInfinity( Int , Int ) 
		| getZero( Int , Int )
	syntax JSPrimitive ::= primAdd( JSPrimitive , JSPrimitive )
			
	rule getInfinity(Sign1:Int, Sign2:Int) 	=> $infinity(Sign1 *Int Sign2)	[structural]
	rule getZero(Sign1, Sign2) 				=> $zero(Sign1 *Int Sign2)		[structural]
	
	--- arithmetic expressions
	rule #div(Left:JSValue, Right:JSValue) 	=> arith("div", Left, Right)
	rule #mod(Left, Right) 		=> arith("mod", Left, Right)
	rule #mul(Left, Right) 		=> arith("mul", Left, Right)
	rule #sub(Left, Right) 		=> arith("sub", Left, Right)
	rule #add(Left, Right) 		=> primAdd(toPrimitive(Left, "N"), toPrimitive(Right, "N"))
	
	--- arithmetic base cases
	rule arith("div", $n(F1:Float), $n(F2:Float)) 	=> $n(F1 /Float F2)		[structural]
	rule arith("mod", $n(F1), $n(F2)) 				=> $n(F1 %Float F2)		[structural]
	rule arith("mul", $n(F1), $n(F2)) 				=> $n(F1 *Float F2)		[structural]
	rule arith("add", $n(F1), $n(F2)) 				=> $n(F1 +Float F2)		[structural]
	rule arith("sub", $n(F1), $n(F2)) 				=> $n(_-Float_(F1, F2))	[structural]

	rule arith("div", $n(I1:Int), $n(I2:Int)) 		=> $n(I1 /Int I2)		[structural]
	rule arith("mod", $n(I1), $n(I2)) 				=> $n(I1 %Int I2)		[structural]
	rule arith("mul", $n(I1), $n(I2)) 				=> $n(I1 *Int I2)		[structural]
	rule arith("add", $n(I1), $n(I2)) 				=> $n(I1 +Int I2)		[structural]
	rule arith("sub", $n(I1), $n(I2)) 				=> $n(_-Int_(I1, I2))	[structural]

	--- number conversions	
	rule arith(OpId, $n(F1), $n(I2)) => arith(OpId, $n(F1), $n(Int2Float(I2)))	[structural]
	rule arith(OpId, $n(I1), $n(F2)) => arith(OpId, $n(Int2Float(I1)), $n(F2))	[structural]

	--- arithmetic with NaN
	rule arith(OpId:String, $nan, Numeric:JSNumeric) => $nan	[structural]
	rule arith(OpId,        Numeric, $nan) 			 => $nan	[structural]
	

	--- ECMA-262 11.5.1
	rule arith("mul", $infinity(Sign1), $infinity(Sign2)) 	=> getInfinity(Sign1, Sign2)	[structural]
	rule arith("mul", $infinity(Sign1), N:JSNonZero) 		=> getInfinity(Sign1, sign(N))	[structural]
	rule arith("mul", N, $infinity(Sign2)) 					=> getInfinity(sign(N), Sign2)	[structural]
	rule arith("mul", $zero(Sign1), $infinity(Sign2)) 		=> $nan 						[structural]
	rule arith("mul", $infinity(Sign1), $zero(Sign2)) 		=> $nan 						[structural]
	rule arith("mul", Num:JSNumber, $zero(Sign2)) 			=> getZero(sign(Num), Sign2)	[structural]
	rule arith("mul", $zero(Sign1), Num)		 			=> getZero(Sign1, sign(Num))	[structural]
	
	--- ECMA-262 11.5.2
	rule arith("div", $infinity(Sign1), $infinity(Sign2)) 	=> $nan							[structural]
	rule arith("div", $infinity(Sign1), Num) 				=> getInfinity(Sign1, sign(Num)) [structural]
	rule arith("div", Num, $infinity(Sign2)) 				=> getZero(sign(Num), Sign2)	[structural]
	rule arith("div", $zero(Sign1), $zero(Sign2)) 			=> $nan							[structural]
	rule arith("div", $zero(Sign1), N) 						=> getZero(Sign1, sign(N))		[structural]
	rule arith("div", N, $zero(Sign2)) 						=> getInfinity(sign(N), Sign2)	[structural]
	
	--- ECMA-262 11.5.3
	rule arith("mod", $infinity(Sign1), Q:JSQuantity)	=> $nan	[structural]
	rule arith("mod", Num, $zero(Sign2)) 				=> $nan	[structural]
	rule arith("mod", Num, $infinity(Sign2)) 			=> Num	[structural]
	rule arith("mod", Z:JSZero, N) 						=> Z	[structural]
	
	--- ECMA-262 11.6.1
	rule primAdd($s(S1:String), $s(S2:String)) 	=> $s(_+String_(S1, S2)) 			[structural]
	rule primAdd($s(S1), NonS2:JSString) 		=> primAdd($s(S1), toString(NonS2))	[structural]
	rule primAdd(NonS1:JSString, $s(S2)) 		=> primAdd(toString(NonS1), $s(S2))	[structural]
	rule primAdd(NonS1, NonS2) 					=> arith("add", NonS1, NonS2)		[structural]
	
	rule arith("add", $infinity(Sign1), $infinity(Sign2)) 	=> $nan					[structural]
	rule arith("add", Num, $infinity(Sign2)) 				=> $infinity(Sign2)		[structural]
	rule arith("add", $infinity(Sign1), Num) 				=> $infinity(Sign1)		[structural]
	rule arith("add", $zero(Sign1), $zero(Sign2)) 			
		=> if Sign1 ==Bool Sign2 then $zero(Sign1) else $zero(1) fi					[structural]
	rule arith("add", $zero(Sign1), N) 						=> N					[structural]
	rule arith("add", N, $zero(Sign2)) 						=> N					[structural]
	
	--- ECMA-262 11.6.3
	rule arith("sub", Left, Right) => arith("add", Left, neg(Right))				[structural]
	
	--- arithmetic conversions
	rule arith(OpId, Numeric:JSNumeric, NonN2) 	  => arith(OpId, Numeric, toNumeric(NonN2)) [structural]
	rule arith(OpId, NonN1:JSNonNumeric, Numeric) => arith(OpId, toNumeric(NonN1), Numeric) [structural]
	rule arith(OpId, NonN1, NonN2:JSNonNumeric)	  => arith(OpId, toNumeric(NonN1), toNumeric(NonN2)) [structural]
	
endkm

kmod JS-COMPARISON is including JS-UNARY + JS-SYNTAX + PL-BUILTINS

	--- ECMA-262 11.8.1-4
	rule #lt(Left:JSValue, Right:JSValue) 	
		=> comparison(primLessThan(toPrimitive(Left, "N"), toPrimitive(Right, "N")), true)
	rule #gt(Left, Right) 	
		=> comparison(primLessThan(toPrimitive(Right, "N"), toPrimitive(Left, "N")), true)
	rule #lte(Left, Right) 	
		=> comparison(primLessThan(toPrimitive(Right, "N"), toPrimitive(Left, "N")), false)
	rule #gte(Left, Right) 
		=> comparison(primLessThan(toPrimitive(Left, "N"), toPrimitive(Right, "N")), false)


	--- ECMA-262 11.8.5
	syntax JSBoolean ::= comparison( JSBooleanPlus , Bool )
	syntax JSBooleanPlus ::= primLessThan( JSValue , JSValue ) 
			| lessThan( JSNumeric , JSNumeric )
	
	rule comparison($undefined, B:Bool)	=> $b(false)	[structural]
	rule comparison($b(B), true)		=> $b(B)		[structural]
	rule comparison($b(B), false)		=> not($b(B))	[structural]
	
	rule primLessThan($s(S1:String), $s(S2:String)) 	=> $b(_<String_(S1, S2)) [structural]
	rule primLessThan(P1:JSPrimitive, NS2:JSNonString) 	=> lessThan(toNumeric(P1), toNumeric(NS2)) [structural]
	rule primLessThan(NS1:JSNonString, P2:JSPrimitive) 	=> lessThan(toNumeric(NS1), toNumeric(P2)) [structural]
	
	rule lessThan($nan, Numeric:JSNumeric) 				=> $undefined [structural]
	rule lessThan(Numeric:JSNumeric, $nan) 				=> $undefined [structural]
	rule lessThan($infinity(Sign:Int), Q:JSQuantity) 	=> $b(_<Int_(Sign, 0)) [structural]
	rule lessThan(Num1:JSNumber, $infinity(Sign)) 		=> $b(_<Int_(0, Sign)) [structural]
	rule lessThan(Num1, Num2:JSNumber) 		=> $b(_<Float_(floatValue(Num1), floatValue(Num2))) [structural]
		
endkm


kmod JS-IDENTITY is including JS-UNARY + JS-SYNTAX
	syntax JSBool ::= identical( JSNonNaN , JSNonNaN )
	
	--- ECMA-262 11.9.4-6
	
	rule #notIdentical(Left:JSValue, Right:JSValue) => not(#identical(Left, Right))
	
	rule #identical($nan, Right) 						=> $b(false)
	rule #identical(Left, $nan) 						=> $b(false)
	rule #identical(Value1:JSNonNaN, Value2:JSNonNaN) 	=> identical(Value1, Value2)

	--- rule #identical(Left, Right) => $b(false) if isEitherNaN(Left, Right)
	--- rule #identical(Left, Right) => identical(Left, Right)
	
	rule identical(Num1:JSNumber, Num2:JSNumber) 
			=> $b(floatValue(Num1) ==Bool floatValue(Num2)) [structural]
	rule identical(Other1:JSNonNumber, Other2:JSNonNumber) 
			=> $b(Other1 ==Bool Other2) [structural]
	
endkm

kmod JS-EQUALITY is including JS-UNARY + JS-SYNTAX + JS-IDENTITY 
	syntax JSBool ::= equal( JSValue , JSValue )
	
	--- ECMA-262 11.9.1-3
	rule #notEqual(Left:JSValue, Right:JSValue) => not(#equal(Left, Right))
	
	rule #equal($nan, Right) 	=> $b(false)
	rule #equal(Left, $nan) 	=> $b(false)
	rule #equal(Left, Right) 	=> $b(true)  if identical(Left, Right)
	rule #equal(Left, Right) 	=> equal(Left, Right) [owise]
	
	macro equal($null, $undefined)			= $b(true)
	macro equal($undefined, $null)			= $b(true)
	
	macro equal(N1:JSNumeric, S2:String)	= #equal(N1, toNumeric(S2))
	macro equal(S1:String, N2:JSNumeric)	= #equal(toNumeric(S1), N2)
	macro equal(B1:JSBool, V2)				= #equal(toNumeric(B1), V2)
	macro equal(V1, B2:JSBool)				= #equal(V1, toNumeric(B2))
	macro equal(N1, O2:JSObject)			= #equal(N1, toPrimitive(O2, "N"))
	macro equal(O1:JSObject, N2)			= #equal(toPrimitive(O1, "N"), N2)
	macro equal(S1, O2)						= #equal(S1, toPrimitive(O2, "N"))
	macro equal(O1, S2)						= #equal(toPrimitive(O1, "N"), S2)
	macro equal(V1, V2)						= $b(false)
endkm

kmod JS-LOGIC is including JS-SYNTAX + JS-CONVERSIONS
	
	--- ECMA-262 11.11
	rule #and(Val:JSValue, Exp)	=> if isTruthy(Val) then Exp else Val fi
	rule #or(Val, Exp:JSValue) 	=> if isTruthy(Val) then Val else Exp fi
endkm


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