module TEST-SYNTAX
  imports UNSIGNED-INT-SYNTAX

  syntax Pgm ::= List{Stmt,""}

  syntax Stmt ::= Exp ";" [strict]

  syntax Exp ::= Int
               | "-" Int
               | Exp "+" Exp [left, strict]
endmodule

module MODE

  syntax Mode ::= "print" | "noprint"

endmodule

module TEST
  imports TEST-SYNTAX
  imports MODE
  imports INT
  imports K-IO
  imports STRING

  configuration <k> $PGM:Pgm </k> <mode parser="MODE, MODE"> $MODE:Mode </mode>

  syntax KResult ::= Int

  rule <k> _I:Int ; => . ...</k> <mode> noprint </mode>
  rule <k> I:Int ; => #write(1, Int2String(I)) ...</k> <mode> print </mode>

  rule I + I2 => I +Int I2
  rule - I => 0 -Int I

  rule S::Stmt S'::Pgm => S ~> S'


endmodule
