// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module CHECKSTRICTBOOLINCLUSION-SYNTAX
// https://github.com/runtimeverification/k/issues/2564
// imports BOOL
    syntax MyBool ::= "mytrue" | "myfalse"
    syntax BExp ::= MyBool | BExp "myand" BExp [strict]

    syntax KResult ::= MyBool

endmodule

module CHECKSTRICTBOOLINCLUSION
    imports CHECKSTRICTBOOLINCLUSION-SYNTAX

    rule mytrue  myand B2 => B2
    rule myfalse myand _  => myfalse

endmodule
