// Copyright (c) 2014 K Team. All Rights Reserved.
module TEST

  configuration <k> $PGM:Exps </k>
  syntax Exp  ::= Id
                | "let" Exp
                > Exp Exp
  syntax Exps ::= List{Exp,","}
endmodule
