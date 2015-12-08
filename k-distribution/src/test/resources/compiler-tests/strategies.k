// Copyright (c) 2014-2015 K Team. All Rights Reserved.
requires "domains.k"

module CONFIGURATION-PRIMITIVES
    syntax K ::= "#RESTORE_CONFIGURATION" "(" K ")"  [klabel(#RESTORE_CONFIGURATION)]
endmodule

module STRATEGY

    syntax #RuleTag ::= r"[a-zA-Z0-9]*"                    [token]

    syntax Strategy ::= "#STUCK"

    syntax StrategyApply ::= "^" #RuleTag                      [klabel(#applyRule)]

    syntax StrategyApplied ::= "~" #RuleTag                    [klabel(#appliedRule)]

    syntax Strategy ::= StrategyApply | StrategyApplied

    syntax Strategy ::= "#START"

    configuration <s> #START:K  </s>
endmodule

module BASIC-STRATEGY
    imports STRATEGY
    imports BOOL
    imports CONFIGURATION-PRIMITIVES

    syntax Strategy ::= Bool

    syntax Hole ::= "#SHOLE" | "#FROZEN" "(" K ")"

    syntax Strategy ::= Hole

    syntax Strategy ::= "if" Strategy "then" Strategy "else" Strategy
                        > Strategy ";" Strategy

    rule <s> if true then B else C => B ...</s>
    rule <s> if false then B else C => C ...</s>

    rule <s> if A:Strategy then B else C => `A ~> #FROZEN(THIS_CONFIGURATION) ~> if #SHOLE then B else C` ...</s> when notBool(isBool(A))
    rule <s> A:Bool ~> if #SHOLE then B else C => if A then B else C ...</s>

    rule <s> false ~> #FROZEN(CONFIGURATION) => #RESTORE_CONFIGURATION(CONFIGURATION) ~> false  ...</s>

    rule <s> true ~> #FROZEN(CONFIGURATION) => true ...</s>

//    rule <s> #STUCK ~> X:StrategyApply => false ...</s>
    rule <s> X:StrategyApplied => true ...</s>


    rule <s> A ; B => A ~> #SHOLE ; B ...</s> when notBool(isBool(A))

    rule <s> A:Bool ~> #SHOLE ; B => A ; B ...</s>

    rule <s> true ; B => B ...</s>

    rule <s> false ; B => false ...</s>

// the second rule is stupid but there a (likely parsing) bug making the first rule not eliminate #STUCK
    rule <s> #STUCK ~> A:StrategyApply => false ...</s>
    rule <s> #STUCK ~> false => false ...</s>
endmodule

module A-STRATEGY
    imports BASIC-STRATEGY
endmodule

module A
    imports A-STRATEGY

    syntax Exp ::= "x" | "y" | "z" | "zz" | "saved" K

    rule x => y                 [tag(xy)]

    rule x => z                 [tag(xz)]

    rule z => zz                [tag(zzz)]

    rule <s> #START => if ^xy ; ^xy then ^xy else ^xz ; ^zzz ; ^zzz </s>

    configuration <t> <k> $PGM </k> initSCell </t>
endmodule
