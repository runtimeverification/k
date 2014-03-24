module TEST

  configuration <k> $PGM:Exp </k>

  syntax Exp ::= Id
               | Exp "." Id
               | "1" Exp "(" Exp ")" [klabel('new_(_))]
               | Exp "(" Exp ")"
               //| "1" Exp             [klabel('new_)]
//new C(x).y(z)
endmodule
