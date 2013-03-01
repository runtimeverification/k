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
        <in> ListItem(I) => . ...</in>
   rule <k> print V:Val => skip ...</k> 
        <out>... . => ListItem(V) </out>
endmodule
