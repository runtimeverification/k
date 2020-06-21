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
rule foo(A) => A
rule foo(B) => B

syntax Int ::= foo2(Foo) [function]
syntax Foo ::= bar() | baz()

rule foo2(bar()) => 0
rule foo2(_) => 0

syntax Int ::= foo3(String) [function]
rule foo3("") => 0
rule foo3(_) => 0

syntax Int ::= foo4(Bytes) [function]
rule foo4(BAR) => lengthBytes(BAR)
rule foo4(BAZ) => lengthBytes(BAZ)

syntax Int ::= foo5(List) [function]
rule foo5(ListItem(_)) => 0
rule foo5(ListItem(_) _) => 0

syntax Int ::= foo6(Map, KItem) [function]
rule foo6(X |-> _, X) => 0
rule foo6(X |-> _ _::Map, X) => 0

syntax Int ::= foo7(Map) [function]
rule foo7(_ |-> _) => 0
rule foo7(_ |-> _ _::Map) => 0

syntax Int ::= foo8(Map, KItem) [function]
rule foo8(X |-> _, X) => 0
rule foo8(_ |-> _, _) => 0
rule foo8(_ |-> _ _::Map, _) => 0

syntax Int ::= foo6(Set, KItem) [function]
rule foo6(SetItem(X), X) => 0
rule foo6(SetItem(X) _, X) => 0

syntax Int ::= foo7(Set) [function]
rule foo7(SetItem(_)) => 0
rule foo7(SetItem(_) _) => 0

syntax Int ::= foo8(Set, KItem) [function]
rule foo8(SetItem(X), X) => 0
rule foo8(SetItem(_), _) => 0
rule foo8(SetItem(_) _, _) => 0

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
rule foo11(_) => 0

syntax KVar ::= "x" [token]
syntax Int ::= foo12(KVar) [function]
rule foo12(x) => 0
rule foo12(_) => 0

syntax Int ::= foo13(StringBuffer) [function]
rule foo13(BAR) => lengthString(StringBuffer2String(BAR))
rule foo13(BAZ) => lengthString(StringBuffer2String(BAZ))

syntax Int ::= used(Foo) [function]
rule used(baz()) => 0

endmodule
