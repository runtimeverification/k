module TEST
  imports INT
  imports STRING
  imports ID

  syntax Int ::= "foo" [macro]
               | "bar" [macro]

  syntax Id ::= "main" [token]

  rule foo => 1 +Int 2
  rule <k> foo => .K </k>

  rule bar => 1 +Int 2 *Int lengthString(Id2String(main) +String substrString("foo", 0, 1))
  rule <k> bar => .K </k>
endmodule
