module TEST
  imports INT
  imports BOOL
  imports MAP

syntax KItem ::= foo(Int) [function]
               | baz(Int) [function]
syntax Bool ::= isZero() [function]

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

rule 4 => ancestor()

syntax KItem ::= ancestor() [function]
rule ancestor() => foo(0)

syntax KItem ::= macro()
rule macro() => ancestor() [macro]

rule 5 => macro()

endmodule
