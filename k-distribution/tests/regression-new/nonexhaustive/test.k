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
rule foo5(ListItem(_)) => 0
rule foo5(ListItem(_) ListItem(_) ListItem(_) _) => 0
rule foo5(ListItem(_) ListItem(0)) => 0

syntax Int ::= foo6(Map, KItem) [function, functional]
rule foo6(.Map, _) => 0
rule foo6(X |-> _ _::Map, X) => 0

syntax Int ::= foo7(Map) [function, functional]
rule foo7(.Map) => 0
rule foo7(_ |-> _) => 0
rule foo7(_ |-> _ _ |-> _ _ |-> _ _::Map) => 0
rule foo7(_ |-> _ 0 |-> _) => 0

syntax Int ::= foo8(Map, KItem) [function, functional]
rule foo8(.Map, _) => 0
rule foo8(X |-> _, X) => 0
rule foo8(_ |-> _, _) => 0
rule foo8(_ |-> _ _ |-> _ _::Map, _) => 0

syntax Int ::= foo9(Map) [function, functional]
rule foo9(_ |-> _) => 0
rule foo9(_ |-> _ _ |-> _ _::Map) => 0

syntax Int ::= foo6(Set, KItem) [function, functional]
rule foo6(.Set, _) => 0
rule foo6(SetItem(X) _::Set, X) => 0

syntax Int ::= foo7(Set) [function, functional]
rule foo7(.Set) => 0
rule foo7(SetItem(_)) => 0
rule foo7(SetItem(_) SetItem(_) SetItem(_) _::Set) => 0
rule foo7(SetItem(_) SetItem(0)) => 0

syntax Int ::= foo8(Set, KItem) [function, functional]
rule foo8(.Set, _) => 0
rule foo8(SetItem(X), X) => 0
rule foo8(SetItem(_), _) => 0
rule foo8(SetItem(_) SetItem(_) _::Set, _) => 0

syntax Int ::= foo9(Set) [function, functional]
rule foo9(SetItem(_)) => 0
rule foo9(SetItem(_) SetItem(_) _) => 0

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

syntax Int ::= used() [function]
rule used() => foo13(.StringBuffer) +Int foo4(.Bytes)

endmodule
