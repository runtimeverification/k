// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module EXPANDMACROREQUIRES
    imports INT
    imports BOOL

    syntax Int  ::= #foo ( Int ) [function]
    syntax Bool ::= #bar ( Int ) [alias]

//    rule #bar ( X ) => X >Int 0 // NOTE I should be defined !!

    rule #foo( X ) => X       requires #bar( X )
endmodule
