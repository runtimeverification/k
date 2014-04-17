// Copyright (c) 2014 K Team. All Rights Reserved.
module TEST

  configuration <k> $PGM:Exp </k>

  syntax Exp ::= Id
               | Exp "." Id
               | "new" Exp "(" Exp ")"
               | Exp "(" Exp ")"
               //| "new" Exp
//new C(x).y(z)
endmodule
