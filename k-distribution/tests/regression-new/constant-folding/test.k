module TEST
  imports INT
  imports STRING
  imports ID

  syntax Int ::= "foo" | "bar"

  syntax Id ::= "main" [token]

  rule foo => 1 +Int 2 [macro]
  rule foo => .K

  rule bar => 1 +Int 2 *Int lengthString(Id2String(main) +String substrString("foo", 0, 1)) [macro]
  rule bar => .K
endmodule
