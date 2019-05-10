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

    rule <s> ~ RT:#RuleTag => . ... </s>
         <trace> ... (.List => ListItem(~ RT)) </trace>
endmodule
