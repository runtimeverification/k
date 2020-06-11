module TEST
  imports INT
  imports ID
  imports MAP

  syntax Exp ::= foo(Exp, Exp) [seqstrict(left; 1; right; 2)]
               | Id "=" Int
               | Id
               | Int
               | l(Exp) [symbol] | m(Exp) [symbol] | r(Exp) [symbol]
  syntax KResult ::= Int

  context alias [left]: HERE [context(l)]
  context alias [middle]: HERE [context(m)]
  context alias [right]: HERE [context(r)]


  configuration <k> $PGM:K </k> <state> .Map </state>

  rule foo(I1:Int, I2:Int) => I1 +Int I2

  rule <k> r(X:Id => I:Int) ...</k> <state>... X |-> I ...</state>
  rule <k> m(X:Id => I:Int) ...</k> <state>... X |-> I ...</state>
  rule <k> l(X:Id = I:Int => I) ...</k> <state> Rho => Rho [ X <- I ] </state>
  rule <k> m(X:Id = I:Int => I) ...</k> <state> Rho => Rho [ X <- I ] </state>

  syntax Exp ::= bar(Exp, Exp, Exp) [seqstrict(left; 1; middle; 2; right; 3)]
  syntax Exp ::= baz(Exp, Exp, Exp) [seqstrict(left; 1, 3; right; 2)]
  syntax Exp ::= qux(Exp, Exp, Exp) [strict(left; 1, 3; right; 2)]

endmodule
