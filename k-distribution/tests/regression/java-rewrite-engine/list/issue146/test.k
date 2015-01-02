// Copyright (c) 2014-2015 K Team. All Rights Reserved.
module TEST
  imports LIST

  configuration <T> <in> ListItem(2) ListItem(1) </in> <k> $PGM:K </k> </T>

  syntax KItem ::= "test"

  rule <in> ListItem(1) V:List ListItem(1) => .List </in>

endmodule
