// Copyright (c) 2013-2015 K Team. All Rights Reserved.
module TEST3
    imports SUBSTITUTION

    syntax Exp ::= Id
                 | Int

    syntax Stmt ::= Id ":=" Exp [strict(2), klabel('_:=_)]
                  | Stmt ";" Stmt [left, klabel('_;_)]
                  | "while" Exp "do" Stmt [klabel('while_do_)]
                  | "{" Stmt "}" [bracket, klabel('{_})]
                  | "L1Stmt" Id ":" Stmt
          > "Labe1Stmt" Id

    syntax Code ::= Exp
                  | Stmt
                  > "L1Code" Id ":" Code
          > "Labe1Code" Id

    syntax KLabel ::= "Label1" Id

    configuration
                    <t1>
                        <k1>
                            $PGM:K
                        </k1>
                    </t1>
endmodule
