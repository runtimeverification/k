/*
*  The code implements the contents of the paper:
*  "Symbolic Execution of Unbounded Object Creation"
*  by Juriaan Rot, Frank de Boer, Marcello Bonsangue
*  (LIACS - Leiden University, and CWI)
*  The focus of this file is on the features specific to
*  the concrete semantics described in Section 3 of the paper.
*/

require silok-basic-semantics

kmod SILOK-CONCRETE-SEMANTICS is including SILOK-BASIC-SEMANTICS

  configuration <T> 
                  <k> .K </k>
                  <state> .Map </state>
                  <pgm> .Map </pgm>
                  <ctr> 0 </ctr>
                </T>

  syntax CellLabel ::= hf

  rule <k> (gvars: LG:ListId  lvars: LL:ListId flds: LF:ListId { Ps:Procs}) 
           => 
           Ps 
       <_/k>
 ---   <state> S:Map => S[bot/List{K}(LG,LL)][wkmap(.Map)/List{K}(LF)] </state>
       <state> S:Map 
               => 
               S[wkbag(<hf>bot|->bot</hf>)/List{K}(LF)][bot/List{K}(LG,LL)] 
       </state>
       <pgm> .Map 
             => 
            ( gvars|->wklist(List{K}(LG)) 
              lvars|->wklist(List{K}(LL))
               flds|->wklist(List{K}(LF))
            )
       </pgm>

  rule <k> X:Id :=new => . <_/k>
       <state_> X|->(_ => C) <_/state>
       <ctr> C:Int => C +Int 1 </ctr>

  rule <k> (X:Id := Y:Id.F:Id) => . <_/k>
---       <state_> X|->(_ => M(J)) Y|->J:IntBot F|->wkmap(M:Map)<_/state>
       <state_> X|->(_ => J) Y|->I:IntBot 
                F|->wkbag(<hf_>I|->J:IntBot<_/hf>)
       <_/state> 

 rule <k> (X:Id.F:Id := Y:Id) => . <_/k>
---         <state_> F|->(wkmap(M) => wkmap(M[J/I])) 
---                  X|->I:IntBot Y|->J:IntBot 
---         <_/state>
         <state_> F|-> wkbag(<hf>M:Map => M[J/I]</hf>) 
                  X|->I:IntBot Y|->J:IntBot 
         <_/state>
 

  rule <k> P:ProcId => B~>restore(S[undef/(G,,F)]) <_/k>
       <state> S:Map => S[bot/L] </state>
       <pgm_> lvars|->wklist(L:List{K}) 
              gvars|->wklist(G:List{K}) 
              flds|->wklist(F:List{K})
              P|->B:B <_/pgm>
  rule <k> restore(S':Map) => . <_/k>
       <state> S => S[S'] </state>

endkm
