module A [private]

  syntax Foo ::= foo() // <- B may not use this symbol

  syntax Foo ::= bam() [public] // <- B may use this symbol

  syntax Foo ::= fu() [private] // <- B may not use this symbol

  syntax Foo ::= "bar" [public, token] // <- B may use this token
               | r"ba." [token, prec(3)]      // <- B may not use this token

  rule foo() => .K
  rule bam() => .K
  rule fu() => .K
  rule bar => .K
  rule baz => .K
endmodule

module B
  imports private A // <- B may use the _public_ syntax of A, but C may not

  syntax Bar ::= a() [public] | b() [private]

  rule foo() => .K
  rule bam() => .K
  rule fu() => .K
  rule bar => .K
  rule baz => .K
  rule a() => .K
  rule b() => .K
endmodule

module C
  imports B

  rule foo() => .K
  rule bam() => .K
  rule fu() => .K
  rule bar => .K
  rule baz => .K
  rule a() => .K
  rule b() => .K
endmodule

module SIGNATURE
  imports C
endmodule
