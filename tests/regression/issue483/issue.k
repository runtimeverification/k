// Copyright (c) 2012-2014 K Team. All Rights Reserved.
module ISSUE

configuration <T><k> 5 </k><env> 5 |-> "5" .Map </env></T>

rule <k> I:Int => M[I] </k>
     <env> M:Map </env>

endmodule
