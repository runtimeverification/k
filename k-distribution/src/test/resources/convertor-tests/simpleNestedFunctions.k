// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
requires "misc.k"

module FUNC
    syntax Foo ::= "foo" Bar    [klabel(foo), function]
    syntax Bar ::= "bar"        [klabel(bar), function]
    syntax Done ::= "done"

    rule `foo`(done) => done
    rule bar => done
endmodule
