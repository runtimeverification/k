// Copyright (c) K Team. All Rights Reserved.
module WIDENINGMACRO
    imports INT
    imports BOOL

    syntax Bool ::= #bar ( Int ) [function]

    rule #bar ( X ) => X
endmodule
