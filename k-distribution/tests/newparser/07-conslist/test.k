// Copyright (c) 2014-2019 K Team. All Rights Reserved.
module TEST

  configuration <k> $PGM:Exp </k>
  syntax Exp  ::= Exp Int | Int
               // List{Int,""}  // TODO: What should we do with lists?
               // Int Exp | Int // TODO: this way it takes a lot of time. See why!

endmodule
