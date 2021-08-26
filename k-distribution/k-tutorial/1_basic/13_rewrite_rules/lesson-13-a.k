module LESSON-13-A-SYNTAX
  imports UNSIGNED-INT-SYNTAX
  imports BOOL-SYNTAX

  syntax Val    ::= Int | Bool
  syntax Exp    ::= Val
                  > left: 
                    Exp "+" Exp
                  | Exp "-" Exp
                  > left: Exp "&&" Exp
endmodule

module LESSON-13-A
  imports LESSON-13-A-SYNTAX
  imports INT
  imports BOOL

  // Two values here - can directly evaluate because we know we're in a fully
  // reduced context.
  rule <k> I1:Int + I2:Int => I1 +Int I2 ... </k>
  rule <k> I1:Int - I2:Int => I1 -Int I2 ... </k>
  rule <k> B1:Bool && B2:Bool => B1 andBool B2 ... </k>

  // Seems to be just to encode the 4 cases - +1, +2, &&1, &&2 so we know which
  // ctor was used to freeze the item down
  syntax KItem  ::= freezer1(Val) | freezer2(Exp)
                  | freezer3(Val) | freezer4(Exp)
                  | freezer5(Val) | freezer6(Exp)

  // If there's a value in the first position, freeze1 it and stick the RHS on
  // top to be evaluated itself
  rule <k> E1:Val + E2:Exp ~> K:K </k> => <k> E2 ~> freezer1(E1) ~> K </k> [priority(51)]
  rule <k> E1:Exp + E2:Exp ~> K:K </k> => <k> E1 ~> freezer2(E2) ~> K </k> [priority(52)]
  rule <k> E1:Val && E2:Exp ~> K:K </k> => <k> E2 ~> freezer3(E1) ~> K </k> [priority(51)]
  rule <k> E1:Exp && E2:Exp ~> K:K </k> => <k> E1 ~> freezer4(E2) ~> K </k> [priority(52)]
  rule <k> E1:Val - E2:Exp ~> K:K </k> => <k> E2 ~> freezer5(E1) ~> K </k> [priority(51)]
  rule <k> E1:Exp - E2:Exp ~> K:K </k> => <k> E1 ~> freezer6(E2) ~> K </k> [priority(52)]

  rule <k> E2:Val ~> freezer1(E1) ~> K:K </k> => <k> E1 + E2 ~> K </k>
  rule <k> E1:Val ~> freezer2(E2) ~> K:K </k> => <k> E1 + E2 ~> K </k>
  rule <k> E2:Val ~> freezer3(E1) ~> K:K </k> => <k> E1 && E2 ~> K </k>
  rule <k> E1:Val ~> freezer4(E2) ~> K:K </k> => <k> E1 && E2 ~> K </k>
  rule <k> E2:Val ~> freezer5(E1) ~> K:K </k> => <k> E1 - E2 ~> K </k>
  rule <k> E1:Val ~> freezer6(E2) ~> K:K </k> => <k> E1 - E2 ~> K </k>
endmodule
