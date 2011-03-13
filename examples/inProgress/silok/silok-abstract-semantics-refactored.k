require silok-basic-semantics


kmod SILOK-ABSTRACT-SEMANTICS-REFACTORING is including SILOK-BASIC-SEMANTICS

// The image of a map, i.e. Map(DomainSet)
  syntax Set ::= values Map
  rule values (Map:Map (K1:K |-> K2:K)) => SetItem(K2) values Map  [structural]
  rule values (.) => . [structural]

// Cardinal of a set.
  syntax Int ::= `| Set `|
  rule | . | => 0 [structural]
  rule | SetItem:SetItem Set:Set | => 1 +Int | Set | [structural]

// firstNotIn Set:Set start I:Int gives the first integer greater or equal to I
// which is not in the Set (assuming Set is a set of integers).
  syntax Int ::= firstNotIn Set start Int
  rule firstNotIn Set start I:Int => I
  if notBool (SetItem(I) in Set) 
  [structural]
  rule firstNotIn Set start I => firstNotIn Set start I +Int 1
  if SetItem(I) in Set 
  [structural]

// firstNotIn Set:Set gives the first positiv integer which is not in Set.
  syntax Int ::= firstNotIn Set 
  rule firstNotIn Set => firstNotIn Set start 0 [structural]

// nextFree(K:K, N:Int, Set:Set) gives the first positiv integer
// which is not in the Set, provided the Set has less than N elements.
// When Set has N elements, nextFree(K, N, Set) returns K. 
  syntax IntBot ::= nextFree ( K , Int , Set ) 
  rule nextFree(IB:K, N:Int, Set) => IB 
  if | Set -Set SetItem(bot) | ==Int N
  [structural]
  rule nextFree(IB, N, Set) => firstNotIn Set
  if | Set -Set SetItem(bot) | <Int N 
  [structural]

// nextFreeValue(K:K, N:Int, Map:Map) is used with K as Map(E), 
// where E is an element in the domain of Map, 
// and where N as the cardinal of the codomain of Map. 
// nextFreeValue(Map(E), N, Map) returns:
// Map(E), if | values Map - bot | = N
// the first positive integer not in the image of the Map, otherwise.  
  syntax IntBot ::= nextFreeValue ( K , Int , Map )
  rule nextFreeValue(IB, N, Map) => nextFree(IB, N, values Map) [structural]


// Obs: frz(G) means G' in the paper.    
  syntax K ::= frz ( K )
// Freezes a list of variables, i.e frzs(G1,,...Gn) is frz(G1),,...frz(Gn)
// which in the paper is defined as \overbar(g').
  syntax List{K} ::= frzs ( List{K} ) 
  rule frzs(.List{K}) => .List{K} [structural]
  rule frzs(K:K,,L:List{K}) => frz(K),,frzs(L) [structural]
// Freezes a set of variables and produces the set of frozen variables
  syntax Set ::= frzSet ( Set )
  rule frzSet(.Set) => .Set [structural]
  rule frzSet(SetItem(K) Set:Set) => SetItem(frz(K)) frzSet(Set) [structural]

// Image of the map Map on the set Set, i.e. Map(Set)
/* !!!Caveat: Set should be included in the domain of Map (i.e. keys(Map))
*             as the current definition does not check this inclusion. 
*/
  syntax Set ::= imgOf Map on Set
  eq imgOf Map on .Set = .Set
  eq imgOf (K |-> K1 Map) on (SetItem(K) Set:Set) = (SetItem(K1) imgOf Map on Set)
---  ceq imgOf Map on (SetItem(K) Set) = imgOf Map on Set if notBool (K in keys Map) 
   
// process(...) runs the algorithm for the return from a procedure call
// processed(...) ends the algorithm.
// We call process with the arguments:
// 		<update>
//                  <sigma>\sigma from the paper</sigma>
//                  <sigma1>\sigma' from the paper</sigma1>
//                  <sigmai>\sigma_i from the paper</sigmai>
//                  <gVarsi-n>gi..gn from the paper</gVarsi-n>
//                  <gVars1-n>g1..gn from the paper</gVars1-n>
//  		</update>
  syntax Map ::= process ( BagItem )
  syntax Map ::= processed ( Map )

// Base Case, when all the global variables g_i were processed.
/* Obs: card gVarsi-n cell content = number of remaining sigmai to update.
* Hence, when gVarsi-n is the empty set, then i=n, 
* and the content of sigmai cell is the \sigma_n in the paper 
*/
  rule process ( 
        <update_>
          <gVarsi-n> .Set </gVarsi-n>
          <sigmai> Map:Map </sigmai>
        <_/update> ) => processed (Map)
---  if Map =/=Bool .Map
  [structural]

// First case of the algorithm, when \sigma(gi)=0, here Gi|->bot in sigma cell.
  rule process(
       <update_>
         <sigma_> Gi:K|->bot <_/sigma>
         <gVarsi-n_> SetItem(Gi)=>. <_/gVarsi-n>
         <sigmai_> Gi|->(_ => bot) <_/sigmai>
       <_/update>)
  [structural]

// Second case of the algorithm, when \sigma(gi)=\sigma(gj), for a j<i.
// Here this is denoted as Gi|->K Gj|->K somewhere in the sigma cell,
// while Gj is in the set of already processed variables, here denoted
// as Gj in gVars1-n cell, but not in the gVarsi-n cell (according to
// the condition notBool (Gj in the content of the gVarsi-n cell))
/* Obs: If K == bot (i.e \sigma(gi)=0) then, with an wellfounded inductive reasoning,
*       also K1 == bot, where Gj|->K1 in sigmai cell
*       (i.e. \sigma_i(gj)=0, because \sigma(gj)=0, and j<i).
*       Hence, in this case, the change applied to the sigmai cell is
*       exactly the one in the case when K=bot (i.e. \sigma(gi)=0),
*       so we do not need to enforce for this rule the condition K=/=bot
*       in order to apply it only when the first rule does not apply,
*       as the algorithm in the paper does. 
*/
  rule process(
       <update_>
         <sigma_> Gi|->K:K Gj:K|->K <_/sigma>
         <gVarsi-n> (SetItem(Gi)=>.) Gs:Set </gVarsi-n>
         <gVars1-n_> SetItem(Gj) <_/gVars1-n>
         <sigmai_> Gj|->K1:K Gi|->(_=>K1) <_/sigmai>
       <_/update>)
  if notBool Gj in (SetItem(Gi) Gs)
  [structural]


// Third case of the algorithm, when \sigma(gi)=\sigma(g'), here denoted by
// Gi|->K frz(G)|->K in the sigma cell (recall that frz(G) is the notation for G').
/* Obs1: It would be less expensive to use the fact that K = K1, 
*        as \sigma(g') = \sigma'(g), and to update Gi in sigmai with K,
*        i.e. \sigma_i(gi := \sigma(g')) as in the paper.
*/
/* Obs2: We argue the ommision of the condition K =/= bot with a similar 
*        reasoning as above in the Obs. for the second case of the algorithm.
*        Moreover, we enforce the application of the current case only on the
*        else branch of the second case by the condition of the rule which states
*        that \sigma(gi) is not in \sigma(g1..gi-1)) based on the fact that:
*        " \exists gj in g1..gi-1 such that \sigma(gi)=\sigma(gj)
*          iff
*          \sigma(gj) in \sigma(g1..gi-1)"
*        
*/
  rule process(
       <update>
         <sigma> Gi|->K:K frz(G:K)|->K Sigma:Map </sigma>
         <sigma1_> G|->K1 <_/sigma1>
         <gVarsi-n> (SetItem(Gi)=>.) Gs:Set </gVarsi-n>
         <gVars1-n> SetItem(G) GGs:Set <_/gVars1-n>
         <sigmai_> Gi|->(_=>K1) <_/sigmai>
       </update>)
  if notBool (K in imgOf Sigma on ((SetItem(G) GGs) -Set (SetItem(Gi) Gs)))
  [structural]

// The last two cases in the algorithm, induced by the rules in nextFreeValue.
/* Obs: The exclusion of the other previous cases is made by the if conditions
*       of the rule, stating that:
*        K=/=bot (\sigma(gi)=/=0) and
*        \sigma(gi) notIn \sigma(g1..gi-1) and
*        \sigma(gi) notIn \sigma(frz(g1..gn)).
*/
  rule process(
       <update_>
         <sigma> Gi|->K Sigma </sigma>
         <gVarsi-n> (SetItem(Gi)=>.) Gs </gVarsi-n>
         <gVars1-n> GGs </gVars1-n>
         <sigmai> Sigmai:Map 
                  => 
                  Sigmai[nextFreeValue(Sigma(Gi), | values Sigma |, Sigma)/Gi] 
         </sigmai>
       <_/update>)
  if K =/=Bool bot
     andBool notBool (K in imgOf Sigma on (GGs -Set (SetItem(Gi) Gs)))
     andBool notBool (K in imgOf Sigma on frzSet(GGs))
  [structural]

---(
  eq process(
       <update>
         <sigma> Gi|->K Sigma </sigma>
         <sigma1> Sigma1:Map </sigma1>
         <gVarsi-n> SetItem(Gi) Gs </gVarsi-n>
         <gVars1-n> GGs </gVars1-n>
         <sigmai> Sigmai:Map </sigmai>
       </update>)
      =
      process(
       <update>
         <sigma> Gi|->K Sigma </sigma>
         <sigma1> Sigma1 </sigma1>
         <gVarsi-n> Gs </gVarsi-n>
         <gVars1-n> GGs </gVars1-n>
         <sigmai>  
              Sigmai[nextFreeValue(Sigma(Gi), | values Sigma |, Sigma)/Gi] 
         </sigmai>
       </update>)
   [owise]
---)
---(
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
      update (Map1 Gelt |-> K frz(Gelt1) |-> K)  mod Map2 --- should be (Gelt1 |-> K1 Map2)  
      /(Gs, (SetItem(Gelt1) GGs), Ls) Map[K1/Gelt]
  if notBool (K in imgOf Map1 on ((SetItem(Gelt1) GGs) -Set (SetItem(Gelt) Gs)))

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
---)
  
// updateFrz Map:Map with Set:Set = Map[Map(Set)/frzs(Set)].
  syntax Map ::= updateFrz Map with Set
  eq updateFrz Map with .Set = Map
  eq updateFrz (Gelt:K |-> K frz(Gelt) |-> K1 Map) with (SetItem(Gelt) Gs:Set)
     =
     (Gelt |-> K frz(Gelt) |-> K (updateFrz Map with Gs)) 


  configuration 
		<T> 
		  <k> .K </k>
                  <state> .Map </state>
		  <pgm> .Map </pgm>
		  <abs> 0 </abs>
		</T>
		<update>
                  <sigma>.Map</sigma>
                  <sigma1>.Map</sigma1>
                  <sigmai>.Map</sigmai>
                  <gVarsi-n>.Set</gVarsi-n>
                  <gVars1-n>.Set</gVars1-n>
  		</update>
		
// At the start of the program execution, al variables, globals LG, locals LL,
// and LG' (here frzs(LG)) are mapped to bot (0 in the paper).
// The cell abs maintians the 2*the no. of global vars. + no. of local vars. 
  rule <k> (gvars: LG:ListId  lvars: LL:ListId { Ps:Procs }) => Ps <_/k>
       <state> S:Map => S[bot/(List{K}(LG,LL),,frzs(List{K}(LG)))] </state>
       <pgm> .Map => ( gvars|->wklist(List{K}(LG)) lvars|->wklist(List{K}(LL)))</pgm>
       <abs> 0 => lengthList{K}(List{K}(LG,LL,LG)) </abs>

// The update upon an assigment with new is made by nextFreeValue explained above.
  rule <k> X:Id :=new => . <_/k>
       <state> S:Map => S[nextFreeValue(S(X), N, S)/X] </state>
       <abs> N </abs>

// Upon a procedure call, the freezed global variables are updated by 
// updateFrz explained above, while the local variables are set to bot.
  rule <k> P:ProcId => B~>restore(S) <_/k>
       <state> S:Map => updateFrz S[bot/LVs] with (Set GVs) </state>
       <pgm_> lvars|->wklist(LVs:List{K}) gvars|->wklist(GVs:List{K}) P|->B:B <_/pgm>


// Upon a returning from a procedure call, the state is processed by the 
// process(...) as explained above, which ends with the processed(Map).
// When processed(...) is matched in the state cell, the processing of the state
// upon return from a procedure call ends, and restore(...) is consumed.
  rule <k> restore(S':Map) <_/k>
       <state> S 
               => 
               process( <update>
                 <sigma> S </sigma>
                 <sigma1> S' </sigma1>
                 <gVarsi-n> Set GVs </gVarsi-n>
                 <gVars1-n> Set GVs </gVars1-n>
                 <sigmai> S' </sigmai>
               </update>)
       </state>
       <pgm_> lvars|->wklist(LVs:List{K}) gvars|->wklist(GVs:List{K}) <_/pgm>


  rule <k> restore(S':Map) => .<_/k>
       <state> processed(S) => S </state>
       <pgm_> lvars|->wklist(LVs:List{K}) gvars|->wklist(GVs:List{K}) <_/pgm>

endkm
