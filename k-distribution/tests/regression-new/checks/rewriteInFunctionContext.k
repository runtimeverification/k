module REWRITEINFUNCTIONCONTEXT
  imports INT
  imports BOOL
  imports MAP

syntax Int ::= foo(Int) [function]

configuration <k> $PGM:K </k> <bar> 0 </bar>

rule [[ foo(0) => 0 ]]
     <bar> 0 => 1 </bar>

endmodule
