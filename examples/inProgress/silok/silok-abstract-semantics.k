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

*** frz(G) <=> G'    
  syntax K ::= frz ( K )
  syntax List{K} ::= frzs ( List{K} ) 
  rule frzs(.List{K}) => .List{K} [structural]
  rule frzs(K:K,,L) => frz(K),,frzs(L) [structural]

*** Image of Map on Set
  syntax Set ::= proj Map on Set
  eq proj Map on .Set = .Set
  eq proj (K |-> K1 Map) on (SetItem(K) Set:Set) = (SetItem(K1) proj Map on Set)
---  ceq proj Map on (SetItem(K) Set) = proj Map on Set if notBool (K in keys Map) 
   

*** update \sigma mod \sigma' / GlobalVars, GlobalVars, LocalVars sigma_i
*** first GlobalVars used for counting, second one for case identification
  syntax Map ::= update Map mod Map `/ `( Set `, Set `, Set `)  Map

*** base case, when all global variables were consumed
  eq update Map1:Map mod Map2:Map /(.Set, Set, Ls:Set) Map 
     = 
     updateLocals Map1 mod Map2 /(Set, Ls) Map

*** rule for bot (i.e. 0 in the paper)
  eq  update (Map1 Gelt:K |-> bot)  mod Map2  
      /((SetItem(Gelt) Gs:Set), GGs:Set, Ls)  Map:Map 
      =
      update (Map1 Gelt |-> bot)  mod Map2  
      /(Gs, GGs, Ls) Map[bot/Gelt]

*** second case, where Gelt is g_i and Gelt1 is g_j, with j<i
  ceq  update (Map1 Gelt |-> K Gelt1:K |-> K)  mod Map2  
      /((SetItem(Gelt) Gs), (SetItem(Gelt1) GGs), Ls) (Gelt1 |-> K1 Map) 
      =
      update (Map1 Gelt |-> K Gelt1 |-> K)  mod Map2  
      /(Gs, (SetItem(Gelt1) GGs), Ls) (Gelt1 |-> K1 Map)[K1/Gelt] 
  if notBool Gelt1 in (SetItem(Gelt) Gs)

*** third case, Gelt1 is g while frz(Gelt1) is g'
  ceq  update (Map1 Gelt |-> K frz(Gelt1) |-> K)  mod (Gelt1 |-> K1 Map2)  
      /((SetItem(Gelt) Gs), (SetItem(Gelt1) GGs), Ls) Map 
      =
      update (Map1 Gelt |-> K frz(Gelt1) |-> K)  mod Map2  
      /(Gs, (SetItem(Gelt1) GGs), Ls) Map[K1/Gelt]
  if notBool (K in proj Map1 on ((SetItem(Gelt1) GGs) -Set (SetItem(Gelt) Gs)))

*** the last two cases, induced by the rules in nextFreeValue
  eq  update Map1  mod Map2 /((SetItem(Gelt) Gs), GGs, Ls) Map 
      =
      update Map1 mod Map2 /(Gs, GGs, Ls) 
      Map[nextFreeValue(Map(Gelt), | values Map |, Map)/Gelt]
  [owise]

*** not in the paper, used for the base case in update
  syntax Map ::= updateLocals Map mod Map `/ `( Set `, Set `)  Map
  eq  updateLocals Map1 mod Map2 /(Gs, .Set) Map = Map 
  eq  updateLocals (Map1 Gelt |-> K frz(Gelt) |-> K)  
      mod (Map2 Gelt |-> K1 Lelt:K |-> K1) 
      /((SetItem(Gelt) Gs:Set), (SetItem(Lelt) Ls))  (Gelt |-> K2 Map)  
      =
      updateLocals (Map1 Gelt |-> K frz(Gelt) |-> K)  
      mod (Map2 Gelt |-> K1 Lelt |-> K1) 
      /((SetItem(Gelt) Gs:Set), Ls)  (Gelt |-> K2 Map)[K2/Lelt] 
  eq  updateLocals Map1 mod Map2 /(Gs, (SetItem(Lelt) Ls)) Map = 
      updateLocals Map1 mod Map2 /(Gs, Ls) Map
  [owise]

  
  syntax Map ::= updateFrz Map with Set
  eq updateFrz Map with .Set = Map
  eq updateFrz (Gelt |-> K frz(Gelt) |-> K1 Map) with (SetItem(Gelt) Gs)
     =
     (Gelt |-> K frz(Gelt) |-> K (updateFrz Map with Gs)) 


  configuration <T> 
		  <k> .K </k>
                  <state> .Map </state>
		  <pgm> .Map </pgm>
		  <abs> 0 </abs>
---  		  <temp> .Set </temp>
                </T>


  rule <k> (gvars: LG:ListId  lvars: LL:ListId { Ps:Procs }) => Ps <_/k>
       <state> S:Map => S[bot/(List{K}(LG,LL),,frzs(List{K}(LG)))] </state>
       <pgm> .Map => ( gvars|->wklist(List{K}(LG)) lvars|->wklist(List{K}(LL)))</pgm>
       <abs> 0 => lengthList{K}(List{K}(LG,LL,LG)) </abs>

  rule <k> X:Id :=new => . <_/k>
       <state> S:Map => S[nextFreeValue(S(X), N, S)/X] </state>
       <abs> N </abs>

  rule <k> P:ProcId => B~>restore(S) <_/k>
       <state> S:Map => updateFrz S[bot/L] with (Set G) </state>
       <pgm_> lvars|->wklist(L:List{K}) gvars|->wklist(G:List{K}) P|->B:B <_/pgm>
  rule <k> restore(S':Map) => . <_/k>
       <state> S => update S mod S'/(Set G, Set G, Set L) S' </state>
       <pgm_> lvars|->wklist(L:List{K}) gvars|->wklist(G:List{K}) <_/pgm>

endkm
