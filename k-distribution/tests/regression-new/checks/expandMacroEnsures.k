// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module EXPANDMACROENSURES
    imports INT
    imports BOOL

    syntax Int  ::= #foo ( Int ) [function]
    syntax Bool ::= #baz ( Int ) [alias]

//    rule #baz ( X ) => X // NOTE I should be defined !!

    rule #foo( X ) => X       ensures  #baz( X )
endmodule
