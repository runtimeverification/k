require silok-basic-semantics


kmod SILOK-ABSTRACT-SEMANTICS is including SILOK-BASIC-SEMANTICS

  syntax Set ::= values Map
  rule values (Map:Map (K1:K |-> K2:K)) => SetItem(K2) values Map  [structural]
  rule values (.) => . [structural]

  syntax Int ::= `| Set `|
  rule | . | => 0 [structural]
  rule | SetItem:SetItem Set:Set | => 1 +Int | Set | [structural]

  syntax Int ::= firstNotIn Set start Int
  rule firstNotIn Set start I:Int => I
  if notBool (SetItem(I) in Set) 
  [structural]
  rule firstNotIn Set start I => firstNotIn Set start I +Int 1
  if SetItem(I) in Set 
  [structural]

  syntax Int ::= firstNotIn Set 
  rule firstNotIn Set => firstNotIn Set start 0 [structural]

  syntax IntBot ::= nextFree ( K , Int , Set ) 
  rule nextFree(IB:K, N:Int, Set) => IB 
  if | Set -Set SetItem(bot) | ==Int N
  [structural]
  rule nextFree(IB, N, Set) => firstNotIn Set
  if | Set -Set SetItem(bot) | <Int N 
  [structural]

  syntax IntBot ::= nextFreeValue ( K , Int , Map )
  rule nextFreeValue(IB, N, Map) => nextFree(IB, N, values Map) [structural]

  syntax PairMapSet ::= pair ( Map , Set )
  syntax Map ::= fst PairMapSet
  syntax Set ::= snd PairMapSet

  eq fst pair (Map, Set) = Map
  eq snd pair (Map, Set) = Set 

  syntax PairMapSet ::= Map / Map `- Set `- Set `| Set
  eq  (Map1:Map Gelt:K |-> K:K Lelt:K |-> K1:K) / 
      (Map2:Map Gelt |-> K Lelt |-> K) - 
      (SetItem(Gelt) Gs:Set) - (SetItem(Lelt) Ls:Set) | Set
      =  
      (Map1 Gelt |-> K) / (Map2 Gelt |-> K Lelt |-> K) 
      - (SetItem(Gelt) Gs:Set) - Ls | Set
  eq  (Map1:Map Lelt |-> K1) / (Map2:Map Lelt |-> bot) 
       - Gs - (SetItem(Lelt) Ls) | Set
       =  
       Map1 / (Map2 Lelt |-> bot) - Gs - Ls | Set
  eq  Map1 / Map2 - Gs - .Set | Set =  pair( Map2[Map1], Set)
  eq  (Map1 Lelt |-> K1) / (Map2:Map Lelt |-> K) 
       - Gs - (SetItem(Lelt) Ls) | Set 
       =  
       Map1 / Map2 - Gs - Ls | (SetItem(Lelt) Set)
  [owise]


  syntax Set ::= leastNotUsedSet Set card Int start Int
  eq leastNotUsedSet Set card 0 start I = .Set
  eq leastNotUsedSet Set card N start I 
     = SetItem(firstNotIn Set start I)
       (leastNotUsedSet Set card (N +Int -1) start (firstNotIn Set start I))
---  if ( 0 <Bool I )
---  if J := firstNotIn Set start I
  [owise]
 

  syntax Set ::= leastNotUsedSet Set card Int
  eq leastNotUsedSet Set card N = leastNotUsedSet Set card N start 0
   
  syntax Map ::= form121Map Set into Set
  eq form121Map .Set into .Set = .Map
  eq form121Map SetItem(K1) Set1:Set into SetItem(K2) Set2:Set 
     = ( K1 |-> K2 ) form121Map Set1 into Set2


  syntax Map ::= Map mod Map `/ `( Set `, Set `)


  eq Map1:Map mod Map2:Map / ( Set1 , Set2 ) 
     =  (fst (Map1 / Map2 - Set1 - Set2 | .Set)) 
     	(form121Map snd (Map1 / Map2 - Set1 - Set2 | .Set) 
	 into leastNotUsedSet (values (fst (Map1 / Map2 - Set1 - Set2 | .Set))) 
	      card | snd (Map1 / Map2 - Set1 - Set2 | .Set) |)
---  if PairMS := Map1 / Map2 - Set1 - Set2 | .Set
***(

  ceq Map1:Map mod Map2:Map / ( Set1 , Set2 ) 
      =  (fst PairMS:PairMapSet) 
         (form121Map snd PairMS 
 	  into leastNotUsedSet values fst PairMS card | snd PairMS |
  if PairMS := Map1 / Map2 - Set1 - Set2 | .Set
***)

  configuration <T> 
		  <k> .K </k>
                  <state> .Map </state>
		  <pgm> .Map </pgm>
		  <abs> 0 </abs>
---  		  <temp> .Set </temp>
                </T>


  rule <k> (gvars: LG:List{Id}  lvars: LL:List{Id} { Ps:Procs }) => Ps <_/k>
       <state> S:Map => S[bot/List{K}(LG,LL)] </state>
       <pgm> .Map => ( gvars|->wklist(List{K}(LG)) lvars|->wklist(List{K}(LL)))</pgm>
       <abs> 0 => lengthList{K}(List{K}(LG,LL)) </abs>

  rule <k> X:Id :=new => . <_/k>
       <state> S:Map => S[nextFreeValue(S(X), N, S)/X] </state>
       <abs> N </abs>

  rule <k> P:ProcId => B~>restore(S) <_/k>
       <state> S:Map => S[bot/L] </state>
       <pgm_> lvars|->wklist(L:List{K}) gvars|->wklist(G:List{K}) P|->B:B <_/pgm>
  rule <k> restore(S':Map) => . <_/k>
       <state> S => S mod S'/(Set G, Set L) </state>
---  	  <state> S => fst (S / S' - Set G - Set L | .Set) </state>
---	  <state> S => form121Map snd (S / S' - Set G - Set L | .Set)
---	 into leastNotUsedSet values fst (S / S' - Set G - Set L | .Set)
---	 card | snd (S / S' - Set G - Set L | .Set) |
--- 	  </state>
---	  <state> S => form121Map Set G into Set L </state>
---	  <temp> _ => values fst (S / S' - Set G - Set L | .Set) </temp>
       <pgm_> lvars|->wklist(L:List{K}) gvars|->wklist(G:List{K}) <_/pgm>

endkm
