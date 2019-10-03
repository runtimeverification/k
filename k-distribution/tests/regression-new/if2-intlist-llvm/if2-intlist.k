// Copyright (c) 2019 K Team. All Rights Reserved.

module IF2-INTLIST-SYNTAX
  imports INT

  syntax IntList ::= List{Int, ""}
  syntax IntList ::= keepSmallerThan40 ( IntList ) [function]
endmodule

module IF2-INTLIST
  imports IF2-INTLIST-SYNTAX

  configuration <k> $PGM:IntList </k>

  rule keepSmallerThan40(I IL) => #if2 I <Int 40
                                    #then I keepSmallerThan40(IL)
                                    #else keepSmallerThan40(IL)
                                  #fi

  rule keepSmallerThan40(.IntList) => .IntList

  syntax IntList ::= "#if2" Bool "#then" IntList "#else" IntList "#fi"   [function]
  rule #if2 C:Bool #then B1 #else _ #fi => B1 requires C
  rule #if2 C:Bool #then _ #else B2 #fi => B2 requires notBool C

endmodule
