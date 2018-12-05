// Copyright (c) 2018 K Team. All Rights Reserved.
module TEST
    imports DOMAINS
    imports STRATEGY
    imports BASIC-STRATEGY

    configuration
      <TEST>
        <s/>
        <k> $PGM:Foo </k>
      </TEST>

    syntax Foo ::= "symbolicFoo" [function]
                 | "foo" | "bar"

    rule <s> ~ S => . ... </s>
    rule symbolicFoo => ?X:Foo
    rule <k> foo => bar ... </k> [tag(F2B)]
    rule <k> bar => foo ... </k> [tag(B2F)]
endmodule
