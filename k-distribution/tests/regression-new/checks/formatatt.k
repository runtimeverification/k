module FORMATATT
  imports BOOL

  syntax Stmt ::= "if" "(" Bool ")" Stmt "else" Stmt [avoid, colors(blue,red,red,blue), format(%1 %2%c%3%r%4 %5 %6 %7)]
endmodule
