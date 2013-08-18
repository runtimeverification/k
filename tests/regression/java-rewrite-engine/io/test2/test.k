require "builtins/list.k"
require "io/io.k"

module TEST
  imports LIST
  imports IO

configuration
    <T>
        <k> $PGM:Stmt </k>
        <in stream="stdin"> .MyList </in>
        <out stream="stdout"> .MyList </out>
    </T>

syntax InputType ::= "str" | "int" | "stmt"
syntax Stmt ::= read(InputType) | print(String)

syntax KResult ::= Int | String

rule <k> read(str) => S ...</k>
     <in> MyListItem(S:String) => .MyList ...</in>
rule <k> read(int) => I ...</k>
     <in> MyListItem(I:Int) => .MyList ...</in>
rule <k> read(stmt) => K2 ...</k>
     <in> MyListItem(K2:Stmt) => .MyList ...</in>

rule <k> print(S:String) => . ...</k>
     <out>... .MyList => MyListItem(S) </out>

endmodule
