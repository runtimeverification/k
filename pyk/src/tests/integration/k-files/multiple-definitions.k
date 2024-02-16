module MULTIPLE-DEFINITIONS
  imports A
  imports B
  imports BOOL
  
  syntax KItem  ::= a(KItem) [klabel(a), symbol]
                  | "b"
                  | "c"
  rule a(X) => b requires isInt(X)
  rule a(X) => b requires notBool isInt(X)
  rule b => c
endmodule

module A
  syntax Int
endmodule

module B
  syntax Int
endmodule
