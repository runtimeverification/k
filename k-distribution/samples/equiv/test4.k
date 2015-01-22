// Copyright (c) 2013-2015 K Team. All Rights Reserved.
module TEST4

    syntax Stmt ::= "abc"
                  | Stmt ";" Stmt [left]
          | "Labe1Stmt" Id

    configuration <k> $PGM:K </k>

endmodule
