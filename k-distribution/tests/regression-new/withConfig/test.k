module TEST
  imports INT
  imports BOOL
  imports MAP

syntax KItem ::= foo(Int) [withConfig, function]
               | baz(Int) [withConfig, function]
syntax Bool ::= isZero() [withConfig, function]

configuration <k> $PGM:K </k> <stuff> <bar> 0 </bar> </stuff>

rule [[ foo(I:Int) => baz(I) ]]
     <bar> I </bar>

rule foo(_) => 1 [owise]

rule [[ baz(I:Int) => false ]]
     <bar> I </bar>

rule true => foo(0)

rule 0 => foo(1)

rule [[ isZero() => X ==Int 0 ]]
     <bar> X </bar>

rule 2 => 3
  requires isZero()

endmodule
