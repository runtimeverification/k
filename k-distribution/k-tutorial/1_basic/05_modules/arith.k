requires "arith-defs.k"

module ARITH-SYNTAX
  imports ATOM-SYNTAX
  imports ADD-SYNTAX
  imports MUL-SYNTAX

  syntax priorities literal atom > unary > mulop > addop
  syntax left addop
  syntax left mulop
endmodule

module ARITH
  imports ARITH-SYNTAX
endmodule
