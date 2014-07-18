// Copyright (c) 2012-2014 K Team. All Rights Reserved.

module ISSUE-SYNTAX
  syntax Stmt ::= "read" String
                | "flush"
        | "getInput"

  syntax Stmts ::= List{Stmt,";"}

  syntax Start ::= Stmts
endmodule

module ISSUE
  imports ISSUE-SYNTAX

  configuration <T>
                    <k> $PGM:K </k>
                    <data> .List </data>
                    <in stream="stdin"> .List </in>
                    <out stream="stdout"> .List </out>
                </T>

  rule <k> read S:String => getInput ...</k>
       <out>... .List => ListItem(S) </out>


  rule <k> getInput => . ...</k>
       <in> ListItem(D:String) => .List ...</in>
       <data>... .List => ListItem(D) </data> [structural]


  rule <k> flush ...</k>
       <data> ListItem(D:String) => .List ...</data>
       <out>... .List => ListItem(D) </out> [structural]

  rule <k> flush => . ...</k>
       <data> .List </data> [structural]

  rule <k> S:Stmt ; Ss:Stmts => S ~> Ss ...</k> [structural]

endmodule
