module TEST
  imports INT
  imports MAP
  imports LIST

  syntax KItem ::= "start"
  configuration <k> start </k>
                <env> 1 |-> ListItem(2) ListItem(3) ListItem(4)
                      5 |-> ListItem(6) ListItem(7)
                      8 |-> ListItem(9) </env>
endmodule
