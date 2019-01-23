// Copyright (c) 2014-2019 K Team. All Rights Reserved.
module TEST

  configuration <k> $PGM:Exps </k>
  syntax Exp ::= Id
               | Exp "+" Exp
  syntax Exps ::= NeList{Exp,","}

endmodule
