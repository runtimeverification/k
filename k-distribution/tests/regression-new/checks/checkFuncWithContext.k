module CHECKFUNCWITHCONTEXT-SYNTAX
  imports INT-SYNTAX
  syntax S ::= func(Int) [function]
  syntax S ::= "a"
endmodule

module CHECKFUNCWITHCONTEXT
  imports CHECKFUNCWITHCONTEXT-SYNTAX
  imports INT
  configuration <k> $PGM:Int </k> <env> .Map </env>
  rule [[ func(1) => a ]]
       <env> .Map </env>
endmodule
