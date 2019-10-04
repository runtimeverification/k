requires "substitution.k"

module TEST-SYNTAX
endmodule

module TEST
  imports TEST-SYNTAX
  imports INT
  imports STRING
  imports BYTES
  imports LIST
  imports MAP
  imports SET
  imports FLOAT
  imports BOOL
  imports KVAR
  imports STRING-BUFFER

syntax Int ::= foo(Int) [function, functional]
rule foo(0) => 0
rule foo(1) => 0
rule foo(2) => 0

syntax Int ::= foo2(Foo) [function, functional]
syntax Foo ::= bar() | baz()

rule foo2(bar()) => 0

syntax Int ::= foo2a(Bar) [function, functional]
syntax Bar ::= stuff(Foo) | Foo
rule foo2a(bar()) => 0
rule foo2a(baz()) => 0
rule foo2a(stuff(bar())) => 0

syntax Int ::= foo3(String) [function, functional]
rule foo3("") => 0
rule foo3("0") => 0
rule foo3("1") => 0
rule foo3("2") => 0

syntax Int ::= foo4(Bytes) [function, functional]

syntax Int ::= foo5(List) [function, functional]
rule foo5(.List) => 0
rule foo5(ListItem(X)) => 0
rule foo5(ListItem(X) ListItem(Y) ListItem(Z) L) => 0
rule foo5(ListItem(X) ListItem(0)) => 0

syntax Int ::= foo6(Map, KItem) [function, functional]
rule foo6(.Map, _) => 0
rule foo6(X |-> Y Z::Map, X) => 0

syntax Int ::= foo7(Map) [function, functional]
rule foo7(.Map) => 0
rule foo7(X |-> Y) => 0
rule foo7(X |-> Y A |-> B C |-> D Z::Map) => 0
rule foo7(X |-> Y 0 |-> B) => 0

syntax Int ::= foo8(Map, KItem) [function, functional]
rule foo8(.Map, _) => 0
rule foo8(X |-> Y, X) => 0
rule foo8(Y |-> Z, X) => 0
rule foo8(Y |-> Z A |-> B W::Map, X) => 0

syntax Int ::= foo9(Map) [function, functional]
rule foo9(X |-> Y) => 0
rule foo9(A |-> B C |-> D M::Map) => 0

syntax Int ::= foo6(Set, KItem) [function, functional]
rule foo6(.Set, _) => 0
rule foo6(SetItem(X) Z::Set, X) => 0

syntax Int ::= foo7(Set) [function, functional]
rule foo7(.Set) => 0
rule foo7(SetItem(X)) => 0
rule foo7(SetItem(X) SetItem(A) SetItem(C) Z::Set) => 0
rule foo7(SetItem(X) SetItem(0)) => 0

syntax Int ::= foo8(Set, KItem) [function, functional]
rule foo8(.Set, _) => 0
rule foo8(SetItem(X), X) => 0
rule foo8(SetItem(Y), X) => 0
rule foo8(SetItem(Y) SetItem(A) W::Set, X) => 0

syntax Int ::= foo9(Set) [function, functional]
rule foo9(SetItem(X)) => 0
rule foo9(SetItem(A) SetItem(C) M) => 0

syntax Int ::= foo10(Float) [function, functional]
rule foo10(0.0) => 0
rule foo10(1.0) => 0
rule foo10(2.0) => 0
rule foo10(0.0F) => 0
rule foo10(0.0f) => 0

syntax Int ::= foo10a(Float) [function, functional]
rule foo10a(0.0f) => 0

syntax Int ::= foo11(Bool) [function, functional]
rule foo11(true) => 0

syntax Int ::= foo11a(Bool) [function, functional]
rule foo11a(false) => 0

syntax KVar ::= "_0" [token] | "_1" [token] | "_2" [token]
syntax Int ::= foo12(KVar) [function, functional]
rule foo12(_0) => 0
rule foo12(_1) => 0
rule foo12(_2) => 0

syntax Int ::= foo13(StringBuffer) [function, functional]

endmodule
