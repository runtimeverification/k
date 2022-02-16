module CONTROL-FLOW-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  imports ID-SYNTAX

  syntax Exp ::= IExp | BExp


  syntax IExp ::= Int
                | Id
                | "(" IExp ")" [bracket]

  syntax IExp ::= IExp "*" IExp [seqstrict]
                | IExp "/" IExp [seqstrict]
                | IExp "+" IExp [seqstrict]
                | IExp "-" IExp [seqstrict]
                | IExp "^" IExp [seqstrict]

  syntax BExp ::= Bool
                | "(" BExp ")" [bracket]

  syntax BExp ::= IExp "==" IExp [seqstrict]
                | IExp "!=" IExp [seqstrict]
                | IExp ">"  IExp [seqstrict]
                | IExp ">=" IExp [seqstrict]
                | IExp "<"  IExp [seqstrict]
                | IExp "<=" IExp [seqstrict]

  syntax BExp ::= BExp "&&" BExp [seqstrict]
                | BExp "||" BExp [seqstrict]


  syntax Stmt ::= Id "=" IExp ";" [strict(2)]
                | Stmt Stmt [left]
                | "if" "(" BExp ")" Block "else" Block [strict(1)]
                | "while" "(" BExp ")" Block

  syntax Block ::= "{" "}"
                 | "{" Stmt "}"
endmodule


module CONTROL-FLOW
  imports CONTROL-FLOW-SYNTAX
  imports INT
  imports BOOL
  imports MAP

  configuration <T>
                  <k> $PGM:Stmt </k>
                  <mem> .Map </mem>
                </T>

  rule <k> S1:Stmt S2:Stmt => S1 ~> S2 ... </k>

  rule <k> X:Id = I:Int ; => . ... </k>
       <mem> M => M [ X <- I ] </mem>

  rule <k> { } => . ... </k>
  rule <k> { S } => S ... </k>

  rule <k> if ( true ) B:Block else _ => B ... </k>
  rule <k> if ( false ) _ else B:Block => B ... </k>

  rule <k> while ( B:BExp ) { S:Stmt } => if ( B ) { S while ( B ) { S } } else { } ... </k>

  rule <k> X:Id => I ... </k>
       <mem> ... X |-> I ... </mem>

  rule <k> I1:Int * I2:Int => I1 *Int I2 ... </k>
  rule <k> I1:Int / I2:Int => I1 /Int I2 ... </k>
  rule <k> I1:Int + I2:Int => I1 +Int I2 ... </k>
  rule <k> I1:Int - I2:Int => I1 -Int I2 ... </k>
  rule <k> I1:Int ^ I2:Int => I1 ^Int I2 ... </k>

  rule <k> I1:Int == I2:Int => I1 ==Int  I2 ... </k>
  rule <k> I1:Int != I2:Int => I1 =/=Int I2 ... </k>
  rule <k> I1:Int >  I2:Int => I1 >Int   I2 ... </k>
  rule <k> I1:Int >= I2:Int => I1 >=Int  I2 ... </k>
  rule <k> I1:Int <  I2:Int => I1 <Int   I2 ... </k>
  rule <k> I1:Int <= I2:Int => I1 <=Int  I2 ... </k>

  rule <k> B1:Bool && B2:Bool => B1 andBool B2 ... </k>
  rule <k> B1:Bool || B2:Bool => B1 orBool  B2 ... </k>

  syntax Bool ::= isKResult(K) [function, symbol]
  rule isKResult(_:Int) => true
  rule isKResult(_:Bool) => true
  rule isKResult(_) => false [owise]
endmodule
