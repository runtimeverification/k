module INVALIDSTRICT
  imports BASIC-K

syntax Foo ::= foo() [strict(1)]

syntax Foo ::= foo(Foo) [strict(2)]

syntax Foo ::= bar(Foo) [strict(foo; bar; 1)]

syntax Bar ::= baz(K) [strict]

syntax Bar ::= stuff(K, Foo) [strict(1)]

syntax Bar ::= stuff2(K, Foo) [strict(2)]

syntax Baz ::= plugh(K)

syntax Baz ::= xyzzy(K)

context plugh(HOLE:K)

context plugh(HOLE)

context alias [x]: xyzzy(HERE)

syntax Baz ::= thingy(K) [seqstrict(x)]

context plugh(HOLE:KItem)

endmodule
