// Copyright (C) 2014 K Team. All Rights Reserved.
module TEST

  configuration <k> $PGM:Exps </k>
  syntax Exp ::= Id
               | Exp "+" Exp
  syntax Exps ::= NeList{Exp,","}

endmodule