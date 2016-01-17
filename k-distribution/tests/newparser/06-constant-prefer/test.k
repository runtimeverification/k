// Copyright (c) 2014-2016 K Team. All Rights Reserved.
module TEST

  configuration <k> $PGM:Exp </k>
  syntax Exp  ::= Int
                | "-" Exp
                > Exp "-" Exp

endmodule
