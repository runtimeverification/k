requires "imp-prime.k"
requires "lambda-prime.k"

module MAIN-SYNTAX

endmodule

module MAIN

imports MAIN-SYNTAX

imports IMP
imports LAMBDA

imports STRATEGY
imports RULE-TAG-SYNTAX

configuration <c>
  <k> $PGM:Cmd </k>
  <s/>
  <impT/>
  <lambdaT/>
</c>

rule <s> ~ a => ^ a ... </s>
rule <s> ~ b => ^ b ... </s>

syntax String ::= RuleTag2String ( #RuleTag ) [function, hook(STRING.token2string)]

rule <s> ~ RT:#RuleTag => . ... </s>
     requires RuleTag2String(RT) =/=String "a"
      andBool RuleTag2String(RT) =/=String "b"

syntax Cmd ::= "check"

endmodule
