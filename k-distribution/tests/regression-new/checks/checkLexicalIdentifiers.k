module CHECKLEXICALIDENTIFIERS-SYNTAX
syntax lexical Foo1 = r"{Foo2}"
syntax lexical Foo2 = r"{Foo3}"
syntax lexical Foo3 = r"{Foo4}"
syntax lexical Foo4 = r"{Foo1}"
syntax lexical Cycle = r"{Cycle}"
syntax lexical Bar1 = r"{Bar1} {Foo1}"
syntax lexical Bad = r"{NotReal}"
syntax Bad1
syntax Bad2 ::= r"{Bad1}"
syntax lexical StartAnchor = r"^foo"
syntax lexical EndAnchor = r"foo$"
endmodule

module CHECKLEXICALIDENTIFIERS
imports CHECKLEXICALIDENTIFIERS-SYNTAX
endmodule
