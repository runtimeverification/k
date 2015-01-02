// Copyright (c) 2012-2015 K Team. All Rights Reserved.
require "int.k"
require "seq.k"

module REF-SYNTAX imports SEQ-SYNTAX
  imports INT-EXP-SYNTAX
  syntax Exp ::= "ref" Exp [ref, strict]
             | "*" Exp [dref, strict]
             > Exp ":=" Exp [assgn, strict(2)]
endmodule

module REF
  imports REF-SYNTAX
  imports SEQ
  imports INT-EXP
  configuration <k> $PGM:Exp </k>
                <mem> .Map </mem>

  context * HOLE := _
  rule <k> ref V:Val => !N:Int ...</k>
       <mem>... .Map => !N |-> V ...</mem>
  rule <k> * N => V ...</k> <mem>... N |-> V ...</mem> [transition]
  rule <k> * N := V => skip ...</k> <mem>... N |-> (_ => V) ...</mem> [transition]
endmodule
