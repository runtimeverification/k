// Copyright (c) 2013-2014 K Team. All Rights Reserved.
module ISSUE

configuration <T color="yellow">
                <k color="green"> $PGM:K </k>
                <state color="red"> .Map </state>
              </T>

syntax KLabel ::= "'Lit" | "'Lookup"  | "'While" | "'Block" | "'ListWrap" | "'Program" | "'Decls"

syntax KResult ::= Int | Bool

rule 'Lit(Str:String) => String2Int(Str)

syntax KLabel ::= "'Plus"       [seqstrict]
rule 'Plus(I1:Int,, I2:Int) => I1 +Int I2

syntax KLabel ::= "'LtEq"       [seqstrict]
rule 'LtEq(I1:Int,, I2:Int) => I1 <=Int I2

syntax KLabel ::= "'LazyAnd"    [strict(1)]
rule 'LazyAnd(false,, _) => false
rule 'LazyAnd(true,, E:K) => E

syntax KLabel ::= "'Not"        [strict]
rule 'Not(B:Bool) => notBool B

rule 'Lookup(Str:String) => String2Id(Str)

rule <k> X:Id => I ...</k>
     <state>... X |-> I:Int ...</state>

syntax KLabel ::= "'Assign"     [strict(2)]
rule 'Assign((Str:String => String2Id(Str)),, _)

rule <k> 'Assign(X:Id,, I:Int) => .K ...</k>
     <state>... X |-> (_ => I) ...</state>

syntax KLabel ::= "'If"         [strict(1)]
rule 'If(B:Bool,, S:K) => 'If(B:Bool,, S,, .K)
rule 'If( true,,   S:K,, _:K) => S
rule 'If(false,, _:K,,   S:K) => S

rule 'While(E:K,, S:K) => 'If(E,, (S ~> 'While(E,, S)),, .K)

rule 'Block(S:K) => S

rule 'ListWrap(S:K,, Ss:KList) => S ~> 'ListWrap(Ss)
rule 'ListWrap(.KList) => .K

rule 'Program(Vars:K,, S:K) => Vars ~> S

rule 'Decls('ListWrap((Str:String => String2Id(Str)),, _))

rule <k> 'Decls('ListWrap((X:Id => .KList),, _)) ...</k>
     <state> Rho:Map (.Map => X |-> 0) </state>
  when notBool(X in keys(Rho))

rule 'Decls('ListWrap(.KList)) => .K

endmodule
