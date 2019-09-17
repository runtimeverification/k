requires "imp-syntax.k"
requires "imp-a.k"
requires "imp-b.k"

module MAIN-SYNTAX

imports IMP-SYNTAX

endmodule

module MAIN

imports MAIN-SYNTAX

imports IMP-A
imports IMP-B

imports STRATEGY
imports RULE-TAG-SYNTAX

configuration <c>
  <k> $PGM:Cmd </k>
  <s/>
  <aT/>
  <bT/>
</c>

rule <s> ~ a => ^ a ... </s>

rule <s> ~ b => ^ b ... </s>

syntax String ::= RuleTag2String ( #RuleTag ) [function, hook(STRING.token2string)]

rule
<s> ~ RT:#RuleTag => . ... </s>
requires RuleTag2String(RT) =/=String "a"
 andBool RuleTag2String(RT) =/=String "b"

syntax Cmd ::= "check"

endmodule
