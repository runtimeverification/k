module ISSUE

syntax Foo ::= bar(Foo, Foo, Foo)
             | baz(Foo, Foo, Foo, Foo)
             | Foo "+" Foo
             | Int
             | "print"
             | Foo Foo [left]

syntax KResult ::= Int

syntax KLabel ::= "lbar"  [strict]
                | "lbaz" [seqstrict]

rule ('bar => lbar) (_)
rule ('baz => lbaz) (_)

configuration <T><k> $PGM:K </k><sum> 0 </sum><out stream="stdout"> .List </out></T>

rule <k> I:Int + I2:Int => I +Int I2 ...</k>
     <sum> _ => I +Int I2 </sum>

rule <k> print => . ...</k>
     <sum> I:Int </sum>
     <out>... . => ListItem(I) </out>

rule F:Foo F2:Foo => F ~> F2

rule lbar(I:Int,, I2:Int,, _) => .
rule lbaz(I:Int,, I2:Int,, I3:Int,, _) => .

endmodule
