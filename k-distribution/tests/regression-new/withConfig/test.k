module TEST
  imports INT
  imports BOOL
  imports MAP

syntax KItem ::= foo(Int) [withConfig, function]
               | baz(Int) [withConfig, function]

configuration <k> $PGM:K </k> <bar> 0 </bar>

rule [[ foo(I:Int) => baz(I) ]]
     <bar> I </bar>

rule foo(_) => 1 [owise]

rule [[ baz(I:Int) => false ]]
     <bar> I </bar>

rule true => foo(0)

rule 0 => foo(1)

endmodule
