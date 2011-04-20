require ../../../../k-prelude


kmod SILOK-SYNTAX is including PL-ID
  
  syntax ListId ::= .ListId | Id | ListId `, ListId [assoc id: .ListId] 

  syntax Pgm ::= gvars: ListId lvars: ListId { Procs }

  syntax Procs ::= ProcId :: B [prec 55 gather(e E)]
  	 	   | Procs Procs [prec 60 gather(e E)]

  syntax ProcId ::= main | breakpoint | p0 | p1 | p2 | p3 | p4

  syntax Id ::= new  

  syntax BExp ::= Id = Id [prec 43] | Id /= Id [prec 43]

  syntax B ::= Id := Id		      	 [prec 45 ]
  	       | B ; B 	     		 [prec 50 gather(e E)] 
  	       | [ BExp ] B 		 [prec 45]
	       | B + B 	   	  	 [prec 48]
	       | ProcId

endkm

kmod SILOK-PROGRAMS is including SILOK-SYNTAX 

syntax Pgm ::= pgm1 | pgm2 | pgm3 | pgm4 | pgm5 | pgm6 | pgm7 

syntax Id ::=	g1 | g2 | g3 
       	      | l1 | l2 | l3

syntax ProcId ::=  p0 | p1 | p2


macro pgm1 =
  gvars: g1, g2
  lvars: l1, l2
  {
  main :: g1 := new; g2 := new; p0 
  p0 :: l1 := g1; l2 := g2; g1 := new; g2 := new; p0 
  }

macro pgm2 =
  gvars: g1, g2
  lvars: l1, l2
  {
  main :: g1 := new; g2 := new; (p0 + p1) 
  p0 :: l1 := g1; g1 := new; p1 
  p1 :: l2 := g2; g2 := new; p0 
  }


endkm


kmod SILOK-ABSTRACT-SEMANTICS is including K + PL-INT + SILOK-PROGRAMS 

  syntax K ::= B | restore ( Map ) | lvars | gvars | ListId 
  	       | Procs | Pgm 
  syntax IntBot ::= Int | bot
  syntax Builtins ::= IntBot
  syntax KResult ::= IntBot | Id

  syntax Bool ::= IntBot !=Int IntBot [ditto]
  rule I:Int !=Int bot => true [structural]
  rule bot !=Int I:Int => true [structural]
  rule bot !=Int bot => false [structural]


  syntax K ::= wklist ( List{K} )

  syntax List{K} ::= `List`{K`} ( ListId )

  rule List{K}(Id:Id,LI:ListId) => Id ,, List{K}(LI) 
       if LI =/=Bool .ListId [structural]
  rule List{K}(Id) => Id [structural]
  rule List{K}(.ListId) => .List{K} [structural]

//@ The image of a map, i.e. Map(DomainSet)
  syntax Set ::= values Map
  rule values (Map:Map (K1:K |-> K2:K)) => SetItem(K2) values Map  [structural]
  rule values (.) => . [structural]

//@ Cardinal of a set.
  syntax Int ::= `| Set `|
  rule | . | => 0 [structural]
  rule | SetItem:SetItem Set:Set | => 1 +Int | Set | [structural]

/*@ 
 firstNotIn Set:Set start I:Int gives the first integer greater or equal to I
 which is not in the Set (assuming Set is a set of integers).
*/
  syntax Int ::= firstNotIn Set start Int
  rule firstNotIn Set start I:Int => I
  if notBool (SetItem(I) in Set) 
  [structural]
  rule firstNotIn Set start I => firstNotIn Set start I +Int 1
  if SetItem(I) in Set 
  [structural]

//@ firstNotIn Set:Set gives the first positiv integer which is not in Set.
  syntax Int ::= firstNotIn Set 
  rule firstNotIn Set => firstNotIn Set start 0 [structural]

/*@
 nextFree(K:K, N:Int, Set:Set) gives the first positiv integer
 which is not in the Set, provided the Set has less than N elements.
 When Set has N elements, nextFree(K, N, Set) returns K. 
*/
  syntax IntBot ::= nextFree ( K , Int , Set ) 
  rule nextFree(IB:K, N:Int, Set) => IB 
  if | Set -Set SetItem(bot) | ==Int N
  [structural]
  rule nextFree(IB, N, Set) => firstNotIn Set
  if | Set -Set SetItem(bot) | <Int N 
  [structural]

/*@
 nextFreeValue(K:K, N:Int, Map:Map) is used with K as Map(E), 
 where E is an element in the domain of Map, 
 and where N as the cardinal of the codomain of Map. 
 nextFreeValue(Map(E), N, Map) returns:
 Map(E), if | values Map - bot | = N
 the first positive integer not in the image of the Map, otherwise.  
*/
  syntax IntBot ::= nextFreeValue ( K , Int , Map )
  rule nextFreeValue(IB, N, Map) => nextFree(IB, N, values Map) [structural]


//@ Obs: frz(G) means G' in the paper.    
  syntax K ::= frz ( K )
/*@
 Freezes a list of variables, i.e frzs(G1,,...Gn) is frz(G1),,...frz(Gn)
 which in the paper is defined as $g'$.
*/
  syntax List{K} ::= frzs ( List{K} ) 
  rule frzs(.List{K}) => .List{K} [structural]
  rule frzs(K:K,,L:List{K}) => frz(K),,frzs(L) [structural]
//@ Freezes a set of variables and produces the set of frozen variables
  syntax Set ::= frzSet ( Set )
  rule frzSet(.Set) => .Set [structural]
  rule frzSet(SetItem(K) Set:Set) => SetItem(frz(K)) frzSet(Set) [structural]

/*@ Image of the map Map on the set Set, i.e. Map(Set)\hfill\break
 !!!Caveat: Set should be included in the domain of Map (i.e. keys(Map))
             as the current definition does not check this inclusion. 
*/
  syntax Set ::= imgOf Map on Set
  eq imgOf Map on .Set = .Set
  eq imgOf (K |-> K1 Map) on (SetItem(K) Set:Set) = (SetItem(K1) imgOf Map on Set)
   
/*@
 \texttt{<update>\ldots</update>} runs the algorithm for the return from a procedure call.
 Here is the description of the content of the update cell:\hfill\break
\texttt{
<update>\hfill\break
\indent <sigma>$\sigma$ from the paper</sigma>\hfill\break
\indent <sigma1>$\sigma'$ from the paper</sigma1>\hfill\break
\indent <sigmai>$\sigma_i$ from the paper</sigmai>\hfill\break
\indent <gi-gn>$g_i..g_n$ from the paper</gi-gn>\hfill\break
\indent <g1-gn>$g_1..g_n$ from the paper</g1-gn>\hfill\break
</update>\hfill\break
}
*/

  syntax CellLabel ::= update | sigma | sigma1 | sigmai | gi-gn | g1-gn

/*@
 Base Case, when all the global variables $g_i$ were processed.
 Obs: card gi-gn cell content = number of remaining sigmai to update.
 Hence, when gi-gn is the empty set, then i=n, 
 and the content of sigmai cell is the $\sigma_n$ in the paper 
*/
  rule <update_>
         <gi-gn> .Set </gi-gn>
         <sigmai> Map:Map </sigmai>
       <_/update>
       =>
       <sigmai> Map:Map </sigmai>
       [structural]

//@ First case of the algorithm, when $\sigma(g_i)=0$, here $G_i \mapsto bot$ in sigma cell.
  rule <update_>
         <sigma_> Gi:K|->bot <_/sigma>
         <gi-gn_> SetItem(Gi)=>. <_/gi-gn>
         <sigmai_> Gi|->(_ => bot) <_/sigmai>
       <_/update> //)
       [structural]

/*@
 Second case of the algorithm, when $\sigma(gi)=\sigma(gj)$, for a $j<i$.
 Here this is denoted as $G_i\mapsto K$ $G_j\mapsto K$ somewhere in the sigma cell,
 while $G_j$ is in the set of already processed variables, here denoted
 as $G_j$ in g1-gn cell, but not in the gi-gn cell (according to
 the condition notBool ($G_j$ in the content of the gi-gn cell))\hfil\break
 Obs: If $K == bot$ (i.e $\sigma(g_i)=0$) then, with an wellfounded inductive reasoning,
       also $K_1 == bot$, where $G_j|->K_1$ in sigmai cell
       (i.e. $\sigma_i(g_j)=0$, because $\sigma(g_j)=0$, and $j<i$).
       Hence, in this case, the change applied to the sigmai cell is
       exactly the one in the case when $K=bot$ (i.e. $\sigma(g_i)=0$),
       so we do not need to enforce for this rule the condition $K \not= bot$
       in order to apply it only when the first rule does not apply,
       as the algorithm in the paper does. 
*/
  rule <update_>
         <sigma_> Gi|->K:K Gj:K|->K <_/sigma>
         <gi-gn> (SetItem(Gi)=>.) Gs:Set </gi-gn>
         <g1-gn_> SetItem(Gj) <_/g1-gn>
         <sigmai_> Gj|->K1:K Gi|->(_=>K1) <_/sigmai>
       <_/update> //)
       if notBool Gj in (SetItem(Gi) Gs)
       [structural]


/*@
 Third case of the algorithm, when $\sigma(gi)=\sigma(g')$, here denoted by
 $G_i\mapsto K$ $frz(G)\mapsto K$ in the sigma cell (recall that $frz(G)$ is the notation for $G'$).\hfil\break
 Obs1: It would be less expensive to use the fact that $K = K_1$, 
        as $\sigma(g') = \sigma'(g)$, and to update Gi in $\sigma_i$ with K,
        i.e. $\sigma_i(g_i := \sigma(g'))$ as in the paper.\hfil\break
 Obs2: We argue the ommision of the condition $K \not= bot$ with a similar 
        reasoning as above in the Obs. for the second case of the algorithm.
        Moreover, we enforce the application of the current case only on the
        else branch of the second case by the condition of the rule which states
        that $\sigma(g_i)$ is not in $\sigma(g_1..g_{i-1})$ based on the fact that:
        " $\exists g_j in g_1..g_{i-1}$ such that $\sigma(g_i)=\sigma(g_j)$.
          iff
          $\sigma(g_j)$ in $\sigma(g_1..g_{i-1})$".
        
*/
  rule <update>
         <sigma> Gi|->K:K frz(G:K)|->K Sigma:Map </sigma>
         <sigma1_> G|->K1 <_/sigma1>
         <gi-gn> (SetItem(Gi)=>.) Gs:Set </gi-gn>
         <g1-gn> SetItem(G) GGs:Set <_/g1-gn>
         <sigmai_> Gi|->(_=>K1) <_/sigmai>
       </update> //)
      if notBool (K in imgOf Sigma on ((SetItem(G) GGs) -Set (SetItem(Gi) Gs)))
      [structural]

/*@ The last two cases in the algorithm, induced by the rules in nextFreeValue.\hfil\break
 Obs: The exclusion of the other previous cases is made by the if conditions
       of the rule, stating that:
        $K\not=bot$ ($\sigma(g_i)\not=0$) and
        $\sigma(g_i) \not\in \sigma(g_1..g_{i-1})$ and
        $\sigma(g_i) \not\in \sigma(frz(g_1..g_n))$.
*/
  rule <update_>
         <sigma> Gi|->K Sigma </sigma>
         <gi-gn> (SetItem(Gi)=>.) Gs </gi-gn>
         <g1-gn> GGs </g1-gn>
         <sigmai> Sigmai:Map 
                  => 
                  Sigmai[nextFreeValue(Sigma(Gi), | values Sigma |, Sigma)/Gi] 
         </sigmai>
       <_/update> //)
       if K =/=Bool bot
       andBool notBool (K in imgOf Sigma on (GGs -Set (SetItem(Gi) Gs)))
       andBool notBool (K in imgOf Sigma on frzSet(GGs))
       [structural]

  
//@ updateFrz Map:Map with Set:Set = Map[Map(Set)/frzs(Set)].
  syntax Map ::= updateFrz Map with Set
  eq updateFrz Map with .Set = Map
  eq updateFrz (Gelt:K |-> K frz(Gelt) |-> K1 Map) with (SetItem(Gelt) Gs:Set)
     =
     (Gelt |-> K frz(Gelt) |-> K (updateFrz Map with Gs)) 


  configuration 
		<T color="pink"> 
		  <k color="green"> .K </k>
          <state color="white"> .Map </state>
          <abs color="violet"> 0 </abs>
          <pgm color="blue"> .Map </pgm>
		</T>

  syntax Bag ::= run ( KLabel )
  rule run (KL:KLabel) => 
       <T_> 
       	   <k> KL(.List{K})~>main </k>
	<_/T> [structural]


  rule ( Ps1:Procs Ps2:Procs ) => Ps1 ~> Ps2
  rule <k> ( P:ProcId :: B:B ) => . <_/k>
       <pgm_> .Map => P|->B <_/pgm>

  rule B1:B;B2:B => B1~>B2  
  rule <k> X:Id:=Y:Id => . <_/k>
       <state_> X|->(_ => I) Y|->I:Int <_/state>
  rule <k> [X=Y]B:B => B <_/k>
        <state_> X|->V:IntBot Y|->V <_/state>
  rule <k> [X/=Y]B:B => B <_/k>
       <state_> X|->V1:IntBot Y|->V2:IntBot <_/state>
  if V1 !=Int V2
  rule <k> B1+B2 => B1 <_/k>
  rule <k> B1+B2 => B2 <_/k>

		
/*@
 At the start of the program execution, al variables, globals LG, locals LL,
 and LG' (here frzs(LG)) are mapped to bot (0 in the paper).
 The cell abs maintains the 2 * no. of global vars. + no. of local vars. 
*/
  rule <k> (gvars: LG:ListId  lvars: LL:ListId { Ps:Procs }) => Ps <_/k>
       <state> S:Map => S[bot/(List{K}(LG,LL),,frzs(List{K}(LG)))] </state>
       <pgm> .Map => ( gvars|->wklist(List{K}(LG)) lvars|->wklist(List{K}(LL)))</pgm>
       <abs> 0 => lengthList{K}(List{K}(LG,LL,LG)) </abs>

//@ The update upon an assigment with new is made by nextFreeValue explained above.
  rule <k> X:Id :=new => . <_/k>
       <state> S:Map => S[nextFreeValue(S(X), N, S)/X] </state>
       <abs> N </abs>

/*@
 Upon a procedure call, the freezed global variables are updated by 
 updateFrz explained above, while the local variables are set to bot.
*/
  rule <k> P:ProcId => B~>restore(S) <_/k>
       <state> S:Map => updateFrz S[bot/LVs] with (Set GVs) </state>
       <pgm_> lvars|->wklist(LVs:List{K}) gvars|->wklist(GVs:List{K}) P|->B:B <_/pgm>


/*@
 Upon a returning from a procedure call, the state is processed by the 
 \texttt{<update>...</update>} as explained above.
*/
  syntax K ::= restored ( Bag )
  rule <k> restore(S':Map)
           =>
           restored(<update>
                      <sigma> S </sigma>
                      <sigma1> S' </sigma1>
                      <gi-gn> Set GVs </gi-gn>
                      <g1-gn> Set GVs </g1-gn>
                      <sigmai> S' </sigmai>
                    </update>
                   )
       <_/k>
       <state> S </state>
       <pgm_> gvars|->wklist(GVs:List{K}) <_/pgm>

  rule <k> restored(<sigmai> S''':Map </sigmai>) => . <_/k>
       <state> S => S''' </state>

endkm
