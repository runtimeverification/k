module TEST

  configuration <k> $PGM:Exp </k>

  syntax Exp ::= Id
               | Exp "." Id
               | "new" Exp "(" Exp ")"
               | Exp "(" Exp ")"
               //| "new" Exp
//new C(x).y(z)
endmodule
