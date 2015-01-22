// Copyright (c) 2013-2015 K Team. All Rights Reserved.
 module TEST-SYNTAX

      syntax Test ::= "nilExp" | return(Test) | returnVal(Val)

      syntax Val ::= "nil"

      syntax KReuslt ::=  Val

endmodule

module TEST

      imports TEST-SYNTAX

      rule <k> nilExp => nil ... </k>
      rule <k> return(Test) => Test ~> returnVal(HOLE) ... </k>
      rule <k> V:Val ~> returnVal(HOLE) => returnVal(V) ... </k>

endmodule

