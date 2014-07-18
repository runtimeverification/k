// Copyright (c) 2013-2014 K Team. All Rights Reserved.
module TEST
  syntax Exp ::= Int | Id
               | "++" Exp [strict]
               > Exp "+" Exp [left]

    context rvalue ( HOLE ) [strict, context(result(RVal)), klabel('rvalue), cell(k)]

    context (HOLE => 'rvalue(HOLE)) + GeneratedFreshVar2:K [left, result(RVal), cell(k)]

    context GeneratedFreshVar3:K + (HOLE => 'rvalue(HOLE)) [left, result(RVal), cell(k)]



  syntax RVal ::= Int

  syntax KItem ::= rvalue(K)

  syntax KResult ::= Id | RVal

  syntax Id ::= Token{"x"}
  syntax Id ::= Token{"y"}

  configuration <k> $PGM:Exp </k>
                <state> x |-> 0 y |-> 0 </state>

  rule <k> ++ X => X ...</k> <state>... X |-> (I:Int => I +Int 1) ...</state>
  rule <k> rvalue(X => I) ...</k> <state>... X |-> I:Int ...</state>

  rule I1:Int + I2:Int => I1 +Int I2
endmodule
