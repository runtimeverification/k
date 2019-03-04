module NESTEDFUNCTIONCONTEXT
  imports INT
  imports BOOL
  imports MAP

syntax Int ::= foo(Int) [withConfig, function]

configuration <k> $PGM:K </k> <bar> 0 </bar> <baz> .K </baz>

rule [[ foo(0) => 1 ]]
     <bar> 0 </bar>
     <baz> 0 </baz>

rule [[[[foo(0) => 1]]
     <bar> 0 </bar>]]
     <baz> 0 </baz>

rule foo(0) => 1
     <baz> [[foo(0)]] <baz> .K </baz> </baz>

endmodule
