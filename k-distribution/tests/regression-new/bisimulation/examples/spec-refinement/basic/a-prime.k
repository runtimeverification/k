requires "imap.k"

module A-SYNTAX

imports INT-SYNTAX

syntax PgmA ::= beginA()
              | loopA(Int, Int)
              | endA()

endmodule

module A-CONFIG

imports A-SYNTAX

imports IMAP
imports INT

configuration <aT>
  <ak> .K </ak>
  <am> .IMap </am>
</aT>

syntax Int ::= hash(Int) [function, smtlib(hash)]

endmodule

module A

imports A-CONFIG

/*
  i = 0
  while (i < 10) {
    m[i+1] = hash(m[i])
    i++
  }
*/

rule <ak> beginA() => loopA(0, 10) ... </ak> [tag(a)]

rule <ak> loopA(I, N) => loopA(I +Int 1, N) ... </ak>
     <am> M => M[I +Int 1 <- hash(M[I])] </am>
    requires 0 <=Int I andBool I <Int N andBool N >=Int 1
    [tag(a)]

rule <ak> loopA(I, N) => endA() ... </ak>
    requires I ==Int N andBool N >=Int 1
    [tag(a)]

endmodule
