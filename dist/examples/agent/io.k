require "seq.k"

module IO-SYNTAX imports SEQ-SYNTAX
  syntax K ::= Int
             | "read"
             | "print" K [strict]
endmodule

  
module IO 
  imports IO-SYNTAX
  imports SEQ
  configuration <k> .K </k>  
                <in> .List </in> <out> .List </out>
   rule <k> read => I:Int ...</k> 
        <in> ListItem(I) => . ...</in>
   rule <k> print V:KResult => skip ...</k> 
        <out>... . => ListItem(V) </out>
endmodule
