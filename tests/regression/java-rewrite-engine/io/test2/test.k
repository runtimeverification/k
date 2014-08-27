// Copyright (c) 2013-2014 K Team. All Rights Reserved.
require "builtins/list.k"
require "io/io.k"

module TEST
  imports LIST
  imports K-IO

configuration
    <T>
        <k> $PGM:Stmt </k>
        <in stream="stdin"> .List </in>
        <out stream="stdout"> .List </out>
    </T>

syntax InputType ::= "str" | "int" | "stmt"
syntax Stmt ::= read(InputType) | print(String)

syntax KResult ::= Int | String

rule <k> read(str) => S ...</k>
     <in> ListItem(S:String) => .List ...</in>
rule <k> read(int) => I ...</k>
     <in> ListItem(I:Int) => .List ...</in>
rule <k> read(stmt) => K2 ...</k>
     <in> ListItem(K2:Stmt) => .List ...</in>

rule <k> print(S:String) => . ...</k>
     <out>... .List => ListItem(S) </out>

endmodule
