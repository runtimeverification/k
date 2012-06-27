

module IF-SYNTAX
  syntax K ::= Bool
             | "if" K "then" K "else" K   [strict(1)]
endmodule

module IF 
  imports IF-SYNTAX

  syntax KResult ::= Bool
  rule if true then E else _ => E
  rule if false then _ else E => E
endmodule
