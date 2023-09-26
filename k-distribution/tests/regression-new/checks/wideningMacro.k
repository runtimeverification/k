// Copyright (c) K Team. All Rights Reserved.
module WIDENINGMACRO
    imports INT
    imports BOOL

    syntax Bool ::= #bar ( KItem ) [function]

    rule #bar ( X::KItem ) => X
endmodule
