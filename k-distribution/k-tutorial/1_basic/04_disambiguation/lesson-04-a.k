module LESSON-04-A

  syntax Exp  ::= "true" | "false"
  
  syntax Stmt ::= "if" "(" Exp ")" Stmt [prefer]
                | "if" "(" Exp ")" Stmt "else" Stmt
                | "{" "}"

endmodule
