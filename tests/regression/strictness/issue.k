module ISSUE

syntax Foo ::= bar(Foo, Foo, Foo) [strict(1, 2)]
             | baz(Foo, Foo, Foo, Foo) [seqstrict(1, 3, 2)]
             | Foo "+" Foo
             | Int
             | "print"
             | Foo Foo [left]

syntax KResult ::= Int

configuration <T><k> $PGM:K </k><sum> 0 </sum><out stream="stdout"> .List </out></T>

rule <k> I:Int + I2:Int => I +Int I2 ...</k>
     <sum> _ => I +Int I2 </sum>

rule <k> print => . ...</k>
     <sum> I:Int </sum>
     <out>... . => ListItem(I) </out>

rule F:Foo F2:Foo => F ~> F2

rule bar(I:Int, I2:Int, _) => .
rule baz(I:Int, I2:Int, I3:Int, _) => .

endmodule
