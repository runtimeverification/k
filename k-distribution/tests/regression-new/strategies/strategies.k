// Copyright (c) 2019 K Team. All Rights Reserved.

module STRATEGIES-SYNTAX
    syntax Pgm ::= "a" | "b" | "c" | "init"
endmodule

module STRATEGIES
    imports STRATEGIES-SYNTAX
    imports STRATEGY
    imports STRATEGY-ABSTRACT
    imports RULE-TAG-SYNTAX

    configuration
      <wrapper>
        <k> $PGM:Pgm </k>
        <trace> .List </trace>
        <s/>
      </wrapper>

    rule <s> ~ a2b => . ... </s>
         <trace> ... (.List => ListItem(~ a2b)) </trace>

    rule <s> ~ a2c => . ... </s>
         <trace> ... (.List => ListItem(~ a2c)) </trace>

    rule <s> ~ c2a => . ... </s>
         <trace> ... (.List => ListItem(~ c2a)) </trace>

    rule <k> init => a ... </k>

    rule <k> a => b ... </k> [tag(a2b)]
    rule <k> a => c ... </k> [tag(a2c)]
    rule <k> c => a ... </k> [tag(c2a)]
endmodule
