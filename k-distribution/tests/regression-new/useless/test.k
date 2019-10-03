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

syntax Int ::= foo(Int) [function]
rule foo(A) => 0
rule foo(B) => 0

syntax Int ::= foo2(Foo) [function]
syntax Foo ::= bar() | baz()

rule foo2(bar()) => 0
rule foo2(BAR) => 0

syntax Int ::= foo3(String) [function]
rule foo3("") => 0
rule foo3(BAR) => 0

syntax Int ::= foo4(Bytes) [function]
rule foo4(BAR) => 0
rule foo4(BAZ) => 0

syntax Int ::= foo5(List) [function]
rule foo5(ListItem(X)) => 0
rule foo5(ListItem(Y) L) => 0

syntax Int ::= foo6(Map, KItem) [function]
rule foo6(X |-> Y, X) => 0
rule foo6(X |-> Y Z::Map, X) => 0

syntax Int ::= foo7(Map) [function]
rule foo7(X |-> Y) => 0
rule foo7(X |-> Y Z::Map) => 0

syntax Int ::= foo8(Map, KItem) [function]
rule foo8(X |-> Y, X) => 0
rule foo8(Y |-> Z, X) => 0
rule foo8(Y |-> Z W::Map, X) => 0

syntax Int ::= foo6(Set, KItem) [function]
rule foo6(SetItem(X), X) => 0
rule foo6(SetItem(X) Z, X) => 0

syntax Int ::= foo7(Set) [function]
rule foo7(SetItem(X)) => 0
rule foo7(SetItem(X) Z) => 0

syntax Int ::= foo8(Set, KItem) [function]
rule foo8(SetItem(X), X) => 0
rule foo8(SetItem(Y), X) => 0
rule foo8(SetItem(Y) W, X) => 0

syntax Int ::= foo10(Float) [function]
rule foo10(0.0) => 0
rule foo10(0.0F) => 0
rule foo10(0.0f) => 0

syntax Int ::= foo10a(Float) [function]
rule foo10a(0.0) => 0
rule foo10a(0.0f) => 0
rule foo10a(0.0p53x11) => 0

syntax Int ::= foo11(Bool) [function]
rule foo11(true) => 0
rule foo11(B) => 0

syntax KVar ::= "x" [token]
syntax Int ::= foo12(KVar) [function]
rule foo12(x) => 0
rule foo12(X) => 0

syntax Int ::= foo13(StringBuffer) [function]
rule foo13(BAR) => 0
rule foo13(BAZ) => 0

endmodule
