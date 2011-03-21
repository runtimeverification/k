
kmod JS-SEMANTICS is including JSON-TO-INFIX

	syntax ::=
		asNumeric ( JS )
		
	macro asNumber(#n(_)) = _
	macro asNumber(#b(true)) = 1
	macro asNumber(#b(false)) = 0
	macro asNumber(#null) = 0
	macro asNumber(#undefined) = 0
	macro asNumber(#s(_)) = number(_)
	macro asNumber(_) = #NaN [owise]

	macro asBoolean(#b(_)) = _
	macro asBoolean(#n(0)) = false
	macro asBoolean(#NaN) = false
	macro asBoolean(#null) = false
	macro asBoolean(#undefined) = false
	macro asBoolean(#s("")) = false
	macro asBoolean(_) = true [owise]

	macro asString(#s(_)) = #invocation(#staticAccess(newString(_),#s("toString")),#comma(.List{JS}))

	--- macro asString(#s(_)) = _
	--- macro asString(#n(_)) = string(_)
	--- macro asString(#b(true)) = "true"
	--- macro asString(#b(false)) = "false"
	--- macro asString(#null) = "null"
	--- macro asString(#undefined) = "undefined"
	--- macro asString(#NaN) = "NaN"

	--- syntax JSArg ::= JSValue
	--- 
	--- syntax JSArgs ::= 
	--- 		.JSArgs | JSArg
	--- 	|	JSArgs JSArgs [assoc comm id: .JSArgs]
	--- 
	--- syntax JS ::= checkArgs( JSArgs )
	--- 
	--- 
	--- macro jsArgs( Exps:List{JS} ) = buildArgs(Exps, .JSArgs)

	macro argsHasNaN(Before:List{JS} , #NaN , After:List{JS}) = true
	macro argsHasNaN(_) = false [owise]
	
	macro argsHasInfinity(Before:List{JS} , #infinity(_) , After:List{JS}) = true
	macro argsHasInfinity(_) = false [owise]
	
	macro argsHasString(Before:List{JS} , #s(_) , After:List{JS}) = true
	macro argsHasString(_) = false [owise]
	
	macro argsHasNumber(Before:List{JS} , #n(_) , After:List{JS}) = true
	macro argsHasNumber(_) = false [owise]
	
	macro argsHasFloat(Before:List{JS} , #n(Num:Float) , After:List{JS}) = true
	macro argsHasFloat(_) = false [owise]
	
	macro argsHasBool(Before:List{JS} , #b(_) , After:List{JS}) = true
	macro argsHasBool(_) = false [owise]

	
--- arithmetic expressions

	macro arith(Op:ArithOp, Left:JS, Right:JS) = #NaN if argsHasNaN(Left, Right)

	macro arith(Op:ArithOp, #infinity(_), #infinity(_)) = #NaN
	macro arith(Op:ArithOp, #infinity(IntA:Int), #n(NumB:Number)) 
		= getInfinity(IntA * NumB)
		= #infinity(I1 *Int I2) if argsHasInfinity(Left, Right)
	
	macro arith(Op:ArithOp, Left:JS, Right:JS) = #infinity if argsHasInfinity(Left, Right)
	
	macro arith(`div, Left:JS, 0) = #NaN if argsHasNaN(Left, Right)

--- macro arith(Op:ArithOp, Left:JS, Right:JS) = #NaN [owise]
	


	macro arith(`mod, Left:JS, 0) = #NaN if argsHasNaN(Left, Right)
	macro arith(`mod, Left:JS, #infinity) = #NaN if argsHasNaN(Left, Right)
	
	
	macro #add(Left:JS, Right:JS) = concat(asString(Left), asString(Right)) 
		if argsHasString(Left , Right)
	macro #add(Left:JS, Right:JS) = fadd(asFloat(Left), asFloat(Right)) 
		if argsHasFloat(Left , Right)
	macro #add(Left:JS, Right:JS) = iadd(asInt(Left), asInt(Right)) [owise]
	
	rule fadd(FloatA:Float, FloatB:Float) => FloatA +Float FloatB
	rule iadd(IntA:Int, IntB:Int) => IntA +Int IntB
	
	macro #sub(Left, Right) = fsub(asFloat(Left), asFloat(Right)) if argsHasFloat(Left , Right)
	macro #sub(Left, Right) = isub(asInt(Left), asInt(Right)) [owise]
	macro #mul(Left, Right) = fmul(asFloat(Left), asFloat(Right)) if argsHasFloat(Left , Right)
	macro #mul(Left, Right) = imul(asInt(Left), asInt(Right)) [owise]
	macro #div(Left, Right) = fdiv(asFloat(Left), asFloat(Right)) if argsHasFloat(Left , Right)
	macro #div(Left, Right) = idiv(asInt(Left), asInt(Right)) [owise]
	
	rule fsub(FloatA:Float, FloatB:Float) => FloatA -Float FloatB
	rule isub(IntA:Int, IntB:Int) => IntA -Int IntB
	rule fmul(FloatA:Float, FloatB:Float) => FloatA *Float FloatB
	rule imul(IntA:Int, IntB:Int) => IntA *Int IntB
	
	
	macro #div(Left:JS, Right:JS) = $div(asNumber(Left), asNumber(Right))
	macro #mod(Left:JS, Right:JS) = $mod(asNumber(Left), asNumber(Right))
	
	
	rule $sub(NumA:Numeric, NumB:Numeric) => NumA -Int NumB
	rule $mul(NumA:Numeric, NumB:Numeric) => NumA +Int NumB
	rule $div(NumA:Numeric, NumB:Numeric) => NumA +Int NumB if NumB =/=Bool 0 
	rule $mod(NumA:Numeric, NumB:Numeric) => NumA +Int NumB if NumB =/=Bool 0 
	
	rule $sub(IntA:Int, NumB:Numeric) => NumA -Int NumB
	rule $mul(NumA:Numeric, NumB:Numeric) => NumA +Int NumB
	rule $div(NumA:Numeric, NumB:Numeric) => NumA +Int NumB if NumB =/=Bool 0 
	rule $mod(NumA:Numeric, NumB:Numeric) => NumA +Int NumB if NumB =/=Bool 0 
	
	| #inc( JS , Bool ) [strict]				--- ++exp OR exp++
	| #dec( JS , Bool ) [strict]				--- --exp OR exp--
	
	| #delete( JS ) [strict]				--- delete TargetExp
	
	| #typeof ( JS ) [strict]				--- typeof Exp
	| #not ( JS ) [strict]				--- ! Exp
	| #neg ( JS ) [strict] 				--- - Exp
	| #plus ( JS ) [strict] 				--- + Exp
	
	| #mul ( JS , JS ) [strict] 			--- Exp * Exp
	| #div ( JS , JS ) [strict] 			--- Exp / Exp
	| #mod ( JS , JS ) [strict] 			--- Exp % Exp
	
	| #add ( JS , JS ) [strict]			--- Exp + Exp
	| #sub ( JS , JS ) [strict] 			--- Exp - Exp
	
	
  rule I1:Int + I2:Int => I1 +Int I2 
  rule _-_(I1,I2) => _-Int_(I1,I2) 
  rule I1 * I2 => I1 *Int I2 
  rule I1 / I2 => I1 /Int I2 if I2 =/=Bool 0 
  rule I1 % I2 => I1 %Int I2 if I2 =/=Bool 0 
  rule - I => -Int I 
  rule I1 < I2 => I1 <Int I2 
  rule I1 <= I2 => I1 <=Int I2 
  rule I1 > I2 => I1 >Int I2 
  rule I1 >= I2 => I1 >=Int I2 
  rule V1:Val == V2:Val => V1 ==Bool V2 
  rule V1 != V2 => V1 =/=Bool V2 
  rule T1:Bool and T2:Bool => T1 andBool T2 
  rule T1 or T2 => T1 orBool T2 
  rule not(T:Bool) => notBool(T) 

-
  rule <k>X:Id => I<_/k> <env_>X |-> N:Nat<_/env> <store_>N |-> I:Int<_/store>
  rule I1:Int + I2:Int => I1 +Int I2 [structural] 
  rule I1 / I2 => I1 /Int I2  if I2 =/=Bool 0 [structural]
  rule <k>++X => I +Int 1<_/k> <env_>X|->N<_/env> <store_>N|->(I => I +Int 1)<_/store>
  rule <k>read=>I<_/k> <in>ListItem(I)=>.<_/in>

  rule I1<=I2 => I1 <=Int I2   [structural] 
  rule not T:Bool => notBool T [structural]
  rule true and B:BExp => B    [structural]
  rule false and B => false    [structural]

  rule {} => .  [structural]
  rule I; => .  [structural]
  rule S1:Stmt S2:Stmt => S1~>S2  [structural]

  rule if  true then S1 else _  => S1 [structural]
  rule if false then _  else S2 => S2 [structural]
  rule <k>while B do S:Stmt => if B then S while B do S else {}<_/k> [structural]


]endkm
