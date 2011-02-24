require silok-basic-semantics

kmod SILOK-ABSTRACT-SEMANTICS is including SILOK-BASIC-SEMANTICS

  syntax Set ::= values Map
  rule values (Map:Map (K1:K |-> K2:K)) => SetItem(K2) values Map  [structural]
  rule values (.) => . [structural]

  syntax Int ::= `| Set `|
  rule | . | => 0 [structural]
  rule | SetItem:SetItem Set:Set | => 1 +Int | Set | [structural]

  syntax Int ::= firstNotIn Map start Int
  rule firstNotIn Map start I:Int => I
  if notBool (SetItem(I) in values Map) [structural]
  rule firstNotIn Map start I => firstNotIn Map start I +Int 1
  if SetItem(I) in values Map [structural]

  syntax Int ::= firstNotIn Map 
  rule firstNotIn Map => firstNotIn Map start 0 [structural]

  syntax IntBot ::= nextFree ( K , Int , Map ) 
  rule nextFree(IB:K, N:Int, Map) => IB 
  if | values Map -Set SetItem(bot) | ==Int N [structural]
  rule nextFree(IB, N, Map) => firstNotIn Map
  if | values Map -Set SetItem(bot) | <Int N [structural]
  
  
  configuration <T> 
		  <k> .K </k>
                  <state> .Map </state>
		  <pgm> .Map </pgm>
		  <abs> 0 </abs>
                </T>


  rule <k> (gvars: LG:List{Id}  lvars: LL:List{Id} { Ps:Procs }) => Ps <_/k>
       <state> S:Map => S[bot/List{K}(LG,LL)] </state>
       <pgm> .Map => ( gvars|->wklist(List{K}(LG)) lvars|->wklist(List{K}(LL)))</pgm>
       <abs> 0 => lengthList{K}(List{K}(LG,LL)) </abs>

  rule <k> X:Id :=new => . <_/k>
       <state> S:Map => S[nextFree(S(X), N, S)/X] </state>
       <abs> N </abs>

endkm
