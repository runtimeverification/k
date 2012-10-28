module ISSUE

configuration <T><k> 5 </k><env> 5 |-> "5" </env></T>

rule <k> I:Int => M(I) </k>
     <env> M:Map </env>

endmodule
