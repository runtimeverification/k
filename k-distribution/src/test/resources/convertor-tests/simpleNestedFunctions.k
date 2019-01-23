// Copyright (c) 2015-2019 K Team. All Rights Reserved.
require "misc.k"

module FUNC
    syntax Foo ::= "foo" Bar    [klabel(foo), function]
    syntax Bar ::= "bar"        [klabel(bar), function]
    syntax Done ::= "done"

    rule `foo`(done) => done
    rule bar => done
endmodule
