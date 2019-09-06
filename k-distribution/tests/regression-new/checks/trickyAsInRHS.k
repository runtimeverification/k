module TRICKYASINRHS
  imports INT
  imports MAP

configuration <k> $PGM:K </k> <map> .Map </map>

syntax KItem ::= foo(Int)
               | bar(Int)

rule <k> foo(I) => bar((I +Int 1) #as INDEX) ...</k>
     <map>... INDEX |-> _ ...</map>

endmodule
