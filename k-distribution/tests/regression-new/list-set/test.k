module TEST
  imports LIST
  imports INT
 
  configuration <k> $PGM:K </k> <list> ListItem(0) ListItem(1) ListItem(2) </list>

  syntax KItem ::= l(Int, Int)

  rule <k> l(I, J) => .K ...</k>
       <list> _ [ I <- J ] </list>
endmodule
