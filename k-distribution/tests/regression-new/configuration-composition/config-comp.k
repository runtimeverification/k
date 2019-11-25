// Copyright (c) 2019 K Team. All Rights Reserved.

module CONFIG-COMP
    imports CONFIG-COMP-1
    imports CONFIG-COMP-2

    configuration
      <example>
        <common/>
        <module1/>
        <module2/>
      </example>
endmodule

module CONFIG-COMP-COMMON
    imports LIST

    configuration
      <common>
        <k> $PGM:Cmds </k>
        <output> .List </output>
      </common>

    syntax Cmd
    syntax Cmds ::= Cmd Cmds
                  | ".Cmds"
endmodule

module CONFIG-COMP-1
    imports CONFIG-COMP-COMMON
    imports INT

    configuration
      <module1>
        <accumulator> 0 </accumulator>
      </module1>

    syntax Int ::= get() [function]
 // -------------------------------
    rule [[ get() => ACCUMULATOR ]]
         <accumulator> ACCUMULATOR </accumulator>

    syntax Cmd ::= "Inc"
 // --------------------
    rule <k> Inc => . ... </k>
         <accumulator> I => I +Int 1 </accumulator>
endmodule

module CONFIG-COMP-2
    imports CONFIG-COMP-COMMON

    configuration
      <module2>
        <stack> .List </stack>
      </module2>

    syntax Cmd ::= "push" Int
                 | "pop"
 // -------------------------
    rule <k> push I => . ... </k>
         <stack> (.List => ListItem( I )) ... </stack>

    rule <k> pop => . ... </k>
         <output> ... (.List => ListItem( I )) </output>
         <stack> (ListItem( I ) => .List) ... </stack>
endmodule
