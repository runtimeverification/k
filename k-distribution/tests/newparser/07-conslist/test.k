// Copyright (c) 2014-2015 K Team. All Rights Reserved.
module TEST

  configuration <k> $PGM:Exp </k>
  syntax Exp  ::= List{Int,""}  // faster like this with the new parser
                //| Int Exp // TODO: this way it takes a lot of time. See why!

endmodule
