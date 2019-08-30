requires "imap.k"

module B-SYNTAX

imports INT-SYNTAX

syntax PgmB ::= beginB()
              | loopB(Int, Int)
              | endB()

endmodule

module B-CONFIG

imports B-SYNTAX

imports IMAP
imports INT

configuration <bT>
  <bk> .K </bk>
  <bm> .IMap </bm>
</bT>

syntax Int ::= sha256(Int) [function, smtlib(sha256)]

syntax Int ::= loc(Int, Int) [function, smtlib(loc)]

endmodule

module B

imports B-CONFIG

/*
  i = 0
  do {
    m[i+1] = sha256(m[i])
    i++
  } while (i < 10)
*/

rule <bk> beginB() => loopB(0, 10) ... </bk> [tag(b)]

rule <bk> loopB(0, N) => loopB(1, N) ... </bk>
     <bm> M => M[loc(0, 1) <- sha256(M[loc(0, 0)])] </bm>
    requires N >=Int 1
    [tag(b)]

rule <bk> loopB(I, N) => loopB(I +Int 1, N) ... </bk>
     <bm> M => M[loc(0, I +Int 1) <- sha256(M[loc(0, I)])] </bm>
    requires 1 <=Int I andBool I <Int N andBool N >=Int 1
    [tag(b)]

rule <bk> loopB(I, N) => endB() ... </bk>
    requires I ==Int N andBool N >=Int 1
    [tag(b)]

endmodule
