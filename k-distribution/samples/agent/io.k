// Copyright (c) 2012-2015 K Team. All Rights Reserved.
require "int.k"
require "seq.k"

module IO-SYNTAX imports SEQ-SYNTAX
  imports INT-EXP-SYNTAX
  syntax Exp ::= "read" [read]
               | "print" Exp [prnt, strict]
endmodule


module IO
  imports IO-SYNTAX
  imports SEQ
  imports INT-EXP
  configuration <k> $PGM:Exp </k>
                <in stream="stdin"> .List </in> <out stream="stdout"> .List </out>
   rule <k> read => I:Int ...</k>
        <in> ListItem(I) => .List ...</in>
   rule <k> print V:Val => skip ...</k>
        <out>... .List => ListItem(V) </out>
endmodule
