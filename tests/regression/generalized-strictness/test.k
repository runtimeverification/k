module TEST
  syntax Exp ::= Int | Id 
               | "++" Exp [strict]
//               > Exp "+" Exp [left, plus, strict, context('rvalue), result(RVal)]
               > Exp "+" Exp [left, strict<k>(all(context('rvalue)))]

  syntax RVal ::= Int

  syntax K ::= rvalue(K) [strict,context(result(RVal))]

  syntax KResult ::= Id | RVal

  syntax Id ::= Token{"x"}
  syntax Id ::= Token{"y"}

  configuration <k> $PGM:Exp </k>
                <state> x |-> 0 y |-> 0 </state>

  rule <k> ++ X => X ...</k> <state>... X |-> (I:Int => I +Int 1) ...</state>
  rule <k> rvalue(X => I) ...</k> <state>... X |-> I:Int ...</state>

  rule I1:Int + I2:Int => I1 +Int I2 
endmodule
