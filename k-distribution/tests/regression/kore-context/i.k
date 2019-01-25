// Copyright (c) 2015-2019 K Team. All Rights Reserved.
require "domains.k"

module I-SYNTAX
imports STRING
imports INT
syntax Stmt ::= "run"
syntax Exp ::= add(Exp,Exp)
             | Int
endmodule

module I

imports I-SYNTAX
imports INT

configuration <T>
  <k> $PGM:K </k>
</T>

syntax KResult ::= Int

rule run => add(add(1,2),3)

rule add(I1:Int,I2:Int) => I1 +Int I2

context add(HOLE:Exp, _:Int) when pred(HOLE)

syntax Bool ::= pred(Exp) [function]
rule pred(add(_:Exp,_:Exp)) => true
rule pred(_) => false [owise]

endmodule
