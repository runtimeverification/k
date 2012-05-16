require "seq.k"

module IO
  imports SEQ
  configuration <k>   .K    </k>  
                <in>  .List </in>
                <out> .List </out>
  syntax K ::= Int
             | "read"
             | "print" K [strict]
  
   rule <k> read => I:Int ...</k> 
        <in> ListItem(I) => . ...</in>
   rule <k> print V:KResult => skip ...</k> 
        <out>... . => ListItem(V) </out>
endmodule
