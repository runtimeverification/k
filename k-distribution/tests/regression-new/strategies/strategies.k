// Copyright (c) 2019 K Team. All Rights Reserved.

module STRATEGIES-SYNTAX
    imports INT

    syntax Pgm ::= "a" | "b" | "c" | "init" | loop ( Int )
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

    rule <k> init => a       ... </k> // tag(regular)
    rule <k> a    => b       ... </k> [tag(a2b)]
    rule <k> a    => c       ... </k> [tag(a2c)]
    rule <k> c    => a       ... </k> [tag(c2a)]
    rule <k> c    => loop(5) ... </k> [tag(c2loop)]

    rule <k> loop(I => I -Int 1) ... </k> requires I >Int 0 [tag(loopRule)]

    rule <s> ~ regular  => . ... </s> <trace> ... (.List => ListItem(~ regular )) </trace>
    rule <s> ~ a2b      => . ... </s> <trace> ... (.List => ListItem(~ a2b     )) </trace>
    rule <s> ~ a2c      => . ... </s> <trace> ... (.List => ListItem(~ a2c     )) </trace>
    rule <s> ~ c2a      => . ... </s> <trace> ... (.List => ListItem(~ c2a     )) </trace>
    rule <s> ~ c2loop   => . ... </s> <trace> ... (.List => ListItem(~ c2loop  )) </trace>
    rule <s> ~ loopRule => . ... </s> <trace> ... (.List => ListItem(~ loopRule)) </trace>
endmodule
