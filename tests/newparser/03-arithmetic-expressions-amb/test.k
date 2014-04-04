// Copyright (C) 2014 K Team. All Rights Reserved.
module TEST

  configuration <k> $PGM:Exp </k>
  syntax Lit  ::= Token{[0-9]+} [onlyLabel]
  syntax Exp  ::= Lit
                | Exp "+" Exp
                | Exp "*" Exp

endmodule
