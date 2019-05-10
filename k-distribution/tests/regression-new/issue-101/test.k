// Copyright (c) 2018-2019 K Team. All Rights Reserved.
module TEST
    imports DOMAINS
    imports STRATEGY
    imports STRATEGY-ABSTRACT
    imports RULE-TAG-SYNTAX

    configuration
      <TEST>
        <s/>
        <k> $PGM:Foo </k>
      </TEST>

    syntax Foo ::= "symbolicFoo" [function]
                 | "foo" | "bar"

    rule <s> ~ S => . ... </s>
    rule symbolicFoo => ?X:Foo
    rule <k> foo => bar ... </k> [tag(f2b)]
    rule <k> bar => foo ... </k> [tag(b2f)]
endmodule
