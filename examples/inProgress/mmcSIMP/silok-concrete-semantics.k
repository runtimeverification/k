require silok-basic-semantics

kmod SILOK-CONCRETE-SEMANTICS is including SILOK-BASIC-SEMANTICS

  configuration <T> 
		  <k> .K </k>
                  <state> .Map </state>
		  <pgm> .Map </pgm>
		  <ctr> 0 </ctr>
                </T>


  rule <k> (gvars: LG:List{Id}  lvars: LL:List{Id} { Ps:Procs}) => Ps <_/k>
       <state> S:Map => S[bot/List{K}(LG,LL)] </state>
       <pgm> .Map => ( gvars|->wklist(List{K}(LG)) lvars|->wklist(List{K}(LL)))</pgm>

  rule <k> X:Id :=new => . <_/k>
       <state_> X|->(_ => C) <_/state>
       <ctr> C:Int => C +Int 1 </ctr>

  rule <k> P:ProcId => B~>restore(S[undef/G]) <_/k>
       <state> S:Map => S[bot/L] </state>
       <pgm> lvars|->wklist(L:List{K}) gvars|->wklist(G:List{K}) P|->B <_/pgm>
  rule <k> restore(S':Map) => . <_/k>
       <state> S => S[S'] </state>


endkm
