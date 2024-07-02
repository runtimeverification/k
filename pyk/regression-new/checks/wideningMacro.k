// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module WIDENINGMACRO
    imports INT
    imports BOOL

    syntax Bool ::= #bar ( Int ) [alias]

    rule #bar ( X ) => X
endmodule
