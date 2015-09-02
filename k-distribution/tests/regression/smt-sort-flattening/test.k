// Copyright (c) 2015 K Team. All Rights Reserved.
module TEST
  syntax S ::= S1           [smt-sort-flatten]
             | S2           [smt-sort-flatten]
  syntax S1 ::= foo1(Int)   [function, smtlib(foo1)]
              | S3
  syntax S2 ::= foo2(Int)   [function, smtlib(foo2)]
              | S3
  syntax S3 ::= "s"
  syntax KItem ::= bar1(Int)
                 | bar2(Int)

  rule 0 => bar1(?_)
  rule bar1(I) => bar2(I)
    requires foo1(I) ==K foo2(I)
  rule bar2(I) => 1
    requires foo1(I) =/=K foo2(I)
endmodule
