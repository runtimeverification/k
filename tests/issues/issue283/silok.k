/*@
*  The code implements the contents of the paper: \\
*  ... abstraction-heap.pdf ...\\
*  by Juriaan Rot, Frank de Boer, Marcello Bonsangue \\
*  (LIACS - Leiden University, and CWI) \\
*/

module SILOK-SYNTAX is 
  

  syntax Ids ::= List{Id,","}

  syntax Pgm ::= "gvars:" Ids "lvars:" Ids "flds:" Ids "{" Procs "}"

  syntax Procs ::= ProcId "::" B           [prec 55 gather(e E)]
                   | Procs Procs         [prec 60 gather(e E)]

  syntax ProcId ::= "main" | "breakpoint" | "p0" | "p1" | "p2" | "p3" | "p4"

  syntax Id ::= "new"  

  syntax FExp ::= Id | Id "." Id [prec 40 gather(e E)]

  syntax BExp ::= Id "=" Id [prec 43] | Id "/=" Id [prec 43]

  syntax B ::= FExp ":=" FExp              [prec 45]
               | B ";" B                   [prec 50 gather(e E)] 
               | "[" BExp "]" B            [prec 45]
               | B + B                     [prec 48]
               | ProcId
               | "read" "(" Id ")"
               | "skip"
end module

require rexp

module K-ADDONS is including #REXP 

/*
/*@ {\it IntBot} = $\mathbb{Z}\cup\{\bot\}$
*/
  syntax IntBot ::= Int | bot

  syntax Builtins ::= IntBot

/*@ Extending $!=_{\it Int}$ for {\it IntBot}
*/
*/
  syntax #Bool ::= IntBot "!=Int" IntBot [ditto]
  eq I:Int !=Int bot = true  --- [structural]
  eq bot !=Int I:Int = true  --- [structural]
  eq bot !=Int bot = false   --- [structural]

//@ Intersection of two sets
  syntax Set ::= Set "nSet" Set
  eq (SI:SetItem Set1:Set) nSet (SI Set2:Set)
     =
     SI (Set1 nSet Set2)
  eq Set1 nSet Set2 = .Set [owise]

//@ Cardinal of a set
  syntax Int ::= "|" Set "|"
  eq | . | = 0 
  eq | SetItem:SetItem Set:Set | = 1 +Int | Set |

---(OBSOLETE
*** Image of Map on Set
  syntax Set ::= "proj" Map "on" Set
  eq proj Map on .Set = .Set
  eq proj (K |-> K1 Map) on (SetItem(K) Set:Set) = (SetItem(K1) proj Map on Set)
---  ceq proj Map on (SetItem(K) Set) = proj Map on Set if notBool (K in keys Map) 
---)   

*** ADDED FROM REFACTORED - same as proj
/*@ ${\tt imgOf} {\it Map} {\tt on} {\it Set} = {\it Map}({\it Set})$, 
    i.e. the image of the map ${\it Map}$ on the set ${\it Set}$\\
 !!!Caveat:\\ 
    ${\it Set}$ should be included in the domain of ${\it Map}$ 
    (i.e. ${\it Set}\subset {\tt keys({\it Map})}$)
    as the current definition does not check this inclusion. 
*/
  syntax Set ::= "imgOf" Map "on" Set
  rule imgOf Map:Map on .Set => .Set
  [structural]
  rule imgOf (K:K |-> K1:K Map) on (SetItem(K) Set:Set) 
       => 
       (SetItem(K1) imgOf Map on Set)
  [structural]
---  ceq imgOf Map on (SetItem(K) Set) = imgOf Map on Set if notBool (K in keys Map) 
***END ADDING

//@ The set of values of a map
  syntax Set ::= "values" Map
  rule values (Map:Map (K1:K |-> K2:K)) => SetItem(K2) values Map  [structural]
  rule values (.) => . [structural]


//@ ${\tt listK}({\it Set})$ transforms the ${\it Set}$ into a list
  syntax List{K} ::= listK "(" Set ")"
  rule listK (SetItem(K) Set:Set) => (K ,, listK(Set)) [structural]
  rule listK (.Set) => .List{K}  [structural]

end module


***********
***SILOK***
***********

module SILOK is including SILOK-SYNTAX + K-ADDONS // + SILOK-PROGRAMS

//@ \subsection{Code for Basics}

//@ Including the syntax of the language in the computation sort {\it K} 
  syntax K ::= B | Ids | Procs | Pgm 
               | "restore" "(" Map ")" 
               | "lvars" | "gvars" | "flds" 
                
//@ The computational atoms are to be included in {\it KResult}
  syntax KResult ::= IntBot | Id 

//@ Wrappers for various sorts used as elements of {\it K}
  syntax K ::= "klist" "(" List{K} ")" 
  syntax K ::= wkbag "(" BagItem ")"

/*@ Transformer for our customized list of variables into a list of computational elements.
*/
  syntax List{K} ::= "id2listk" "(" Ids ")"

  rule id2listk(_`,_(Id:Id,LI:Ids)) => Id ,, id2listk(LI) 
       if LI =/=Bool .List{","} [structural]
  rule id2listk(Id) => Id [structural]
  rule id2listk(.List{","}) => .List{K} [structural]

// End Code for Basics

//@ \subsection{General Underwires for Abstraction}

//@ Formatting logical variables
  syntax Id ::= "v"                  *** dangerous!!!
  syntax K ::= Id "-" Int

/*@ ${\tt frz}(g) \equiv g'$ \\
    ${\tt frzs}(g_1..g_n) \equiv g'_1..g'_n$
*/
  syntax K ::= "frz" "(" K ")"
  syntax List{K} ::= "frzs" "(" List{K} ")" 
  rule frzs(.List{K}) => .List{K} [structural]
  rule frzs(K:K,,L) => frz(K),,frzs(L) [structural]


/*@ ${\tt firstNotIn}\ {\it Set}\ {\tt start}\ I = 
{\it min}\{ n\in \mathbb{N} | n\notin {\it Set}, n\geq I\}$
*/
  syntax Int ::= "firstNotIn" Set "start" Int
  rule firstNotIn Set start I:Int => I
  if notBool (SetItem(I) in Set) 
  [structural]
  rule firstNotIn Set start I => firstNotIn Set start I +Int 1
  if SetItem(I) in Set 
  [structural]

/*@ {\tt firstNotIn} {\it Set} = {\it min}\{$n\in \mathbb{N} | n\notin {\it Set}$\}
*/
  syntax Int ::= "firstNotIn" Set 
  rule firstNotIn Set => firstNotIn Set start 0 [structural]


--- NEW ENTRIES
/*@  ${\tt listFirstNotIn}\ {\it Set}\ {\tt count}\ N$ = 
       the list of the first $N$ positive integers not in ${\it Set}$\\
     ${\tt listFirstNotIn}\ {\it Set}\ {\tt start}\ I\ {\tt count}\ N$ = 
       the list of the first $N$ integers greater than $I$ not in ${\it Set}$\\
     ${\tt seqListFstNotIn}(I,{\it Set}, N)$ = 
    helper for ${\tt listFirstNotIn}\ {\it Set}\ {\tt start}\ I\ {\tt count}\ N$
*/
  syntax List{K} ::= "listFirstNotIn" Set "count" Int
  syntax List{K} ::= "listFirstNotIn" Set "start" Int "count" Int
  syntax List{K} ::= "seqListFstNotIn" "(" Int "," Set "," Int ")"

  rule listFirstNotIn Set count N:Int => listFirstNotIn Set start 0 count N 
  [structural]

  rule listFirstNotIn Set start I count 0 => .List{K}
  [structural]
  rule listFirstNotIn Set start I count N 
       =>
       seqListFstNotIn(firstNotIn Set start I, Set, N)
  if (N >Int 0)
  [structural]

  rule seqListFstNotIn(I, Set, N) 
       => 
       I ,, (listFirstNotIn Set start (I +Int 1) count (N +Int -1))
  [structural]

--- end NEW ENTRIES

---(OBSOLETE
/*@ {\tt nextFree}$(K,I,{\it Set})$ = 
*/
  syntax IntBot ::= "nextFree" "(" K "," Int "," Set ")" 
  rule nextFree(IB:K, N:Int, Set) => IB 
  if | Set -Set SetItem(bot) | ==Int N
  [structural]
  rule nextFree(IB, N, Set) => firstNotIn Set
  if | Set -Set SetItem(bot) | <Int N 
  [structural]

  syntax IntBot ::= "nextFreeValue" "(" K "," Int "," Map ")"
  rule nextFreeValue(IB, N, Map) => nextFree(IB, N, values Map) 
  [structural]
---)

/*@  ${\tt setFirstNotIn}\ {\it Set}\ {\tt card} N$ = 
       the set of the first $N$ positive integers not in ${\it Set}$\\
     ${\tt setFirstNotIn}\ {\it Set}\ {\tt card}\ N\ {\tt start} I$ = 
       the set of the first $N$ integers greater than $I$ not in ${\it Set}$\\
 (these are defined for type convenience and for efficiency reasons)
*/
  syntax Set ::= "setFirstNotIn" Set "card" Int
  syntax Set ::= "setFirstNotIn" Set "start" Int "card" Int

  rule setFirstNotIn Set card N => setFirstNotIn Set start 0 card N
  [structural]

  eq setFirstNotIn Set  start I card 0 = .Set
  eq setFirstNotIn Set start I card N 
     = SetItem(firstNotIn Set start I)
       (setFirstNotIn Set start (firstNotIn Set start I) card (N +Int -1))
---  if ( 0 <Bool I )
---  if J := firstNotIn Set start I
  [owise]
 
--- end from old abstract


// \subsection*{New Entries for the Current Abstraction}
--- NEWS4FIELDS

//@ \subsection{Code for Reachable Objects $\mathcal{R}_H$}
--- reach


/*@ ${\tt reach}(H,F) = \mathcal{R}_H$\\
    ${\tt reachFromSet}(X,H,F) = \mathcal{R}_H(X)$ (with the helper {\tt reachFromSetAcc})\\
    ${\tt reachFromElt}(o,H,F) = \mathcal{R}_H(o)$\\
    ${\tt reachFromVSet}({\it Var},H,F) = \mathcal{R}_H({\it Var})$\\ 
    ${\tt reachFromList}({\it ListVar},H,F)$ added for type convenience\\ 
*/
  syntax Set ::= "reach" "(" Map "," List{K} ")" 
  syntax Set ::= "reachFromSet" "(" Set "," Map "," List{K} ")"
  syntax Set ::= "reachFromSetAcc" "(" Set "," Map "," List{K} "," Set ")"
  syntax Set ::= "reachFromElt" "(" K "," Map "," List{K} "," Set ")"

  syntax Set ::= "reachFromList" "(" List{K} "," Map , List{K} ")"
  syntax Set ::= reachFromVSet ( Set , Map , List{K} )

  rule reach(Heap:Map, F:List{K}) 
       =>
       reachFromSet(values (Heap[undef/F]), Heap, F)
  [structural]

  rule reachFromList(LVars:List{K}, Heap, F) 
       =>
       reachFromSet((Set Heap(LVars)), Heap, F)
  [structural]

  rule reachFromVSet(Set, Heap, F) => reachFromSet((imgOf Heap on Set), Heap, F)
  [structural]

  rule reachFromSet(Set, Heap, F) => reachFromSetAcc(Set, Heap, F, .Set)
  [structural]

  rule reachFromSetAcc(SetItem(K:K) Set:Set, Heap, F , Aux:Set)
       =>
       reachFromSetAcc(Set, Heap, F , (RElt Aux)) --- RElt
  where RElt = reachFromElt(K, Heap, F , Aux )
  [structural]
  rule reachFromSetAcc(.Set, Heap, F, Aux) => Aux --- .Set
  [structural]

  rule reachFromElt(bot, Heap, F , Aux) => .Set --- SetItem(bot)
  [structural]
  rule reachFromElt(K:K, Heap, F, (SetItem(K) Aux)) => .Set
  if (K =/=Bool bot)
  [structural]
  rule reachFromElt(K:K, Heap, F, Aux) 
       => 
       SetItem(K) reachFromSetAcc(flatten(Heap(F), K), Heap, F, (SetItem(K) Aux))
  if (K =/=Bool bot) andBool notBool(K in Aux)
  [structural]


/*@ ${\tt flatten}(H(F){\it List}, o)$ = $H(F)(o)$ = $\cup_{f\in F}H(f)(o)$ is a helper for $\mathcal{R}_H$
*/
  syntax Set ::= "flatten" "(" List{K} "," K ")"
  rule flatten(.List{K}, K:K) => .Set
  [structural]
  rule flatten( (wkbag(<hf_> K|->K':K <_/hf>),,Ks:List{K}),  K )
       =>
       SetItem(K') flatten(Ks, K) 
  [structural]
  rule flatten( (wkbag(<hf>Map</hf>),,Ks:List{K}),  K )
       =>
       flatten(Ks, K)
  if notBool $hasMapping(Map,K) 
  [structural]


--- endreach

//@ \subsection{Code for Renaming Function $\rho$}
--- rename

/*@ {\tt objRename}$(k,o',o)$ = $k[o'/o]$ 
*/
  syntax K ::= "objRename" "(" K "," K "," K ")"
  eq objRename(O, O', O) = O'  
  eq objRename(K, O', O) = K [owise]

/*@ {\tt mapRename}$({\it Map},o',o)$ = ${\it Map}[o'/o]$ is a helper for $\rho$ on fields
*/    
  syntax Map ::= "mapRename" "(" Map "," K "," K ")"
  syntax Map ::= "mapRenameQ" "(" Map "," K "," K "," K ")"

  rule mapRename(Map, O', O) => mapRenameQ(Map, O', O, Map(O))
  [structural]
---!!!  eq mapRename(((O' |-> K) Map), O', O) = (O |-> objRename(K,O',O)) mapRename(Map,O',O)

  rule mapRenameQ(((O |-> K) Map), O', O, K) => (O' |-> objRename(K,O',O)) mapRenameQ(Map,O',O,K)
  [structural]
  rule mapRenameQ(((O' |-> K') Map), O', O, K) => (O |-> objRename(K,O',O)) mapRenameQ(Map,O',O,K)
  [structural]
  rule mapRenameQ(((Q |-> K') Map), O', O, K) => (Q |-> objRename(K',O',O)) mapRenameQ(Map,O',O,K)
  if _andBool_((Q =/=Bool O), (Q =/=Bool O'))
  [structural]
---!!!CHECK WITH JURRIAAN:  if Q =/=Bool O'
  rule mapRenameQ(.Map, O', O, K) => .Map
  [structural]

/*@ {\tt rho}$(H, o\mapsto o', GLs, F)$ = $\rho(H, o\rightarrow o')$, where $GLs$ is the list of global and local variables, while $F$ is the list of fields.\\
    {\tt rhoVars}$(H, o\mapsto o', GLs)$ = $\rho(H, o\rightarrow o')(v)$ foreach $v\in GLs$\\
    {\tt rhoFlds}$(H, o\mapsto o', F)$ = $\rho(H, o\rightarrow o')(f)$ foreach $f\in F$
*/
  syntax Map ::= "rho" "(" Map "," MapItem "," List{K} "," List{K} ")"
  syntax Map ::= rhoVars "(" Map "," MapItem "," List{K} ")"
  syntax Map ::= rhoFlds "(" Map "," MapItem "," List{K} ")"


  rule rho( Heap, (O:K |-> O':K), GLs:List{K}, F:List{K})
       =>
       rhoFlds(rhoVars(Heap,  (O:K |-> O':K), GLs),  (O:K |-> O':K), F)
  [structural]

  rule rhoVars((Var|->Q:K Heap),  (O:K |-> O':K), (Var:K,,VarLs:List{K}))
       =>
       rhoVars((Var|->objRename(Q,O',O) Heap),  (O:K |-> O':K), VarLs:List{K})
  [structural]
  rule rhoVars(Heap,  (O:K |-> O':K), .List{K}) 
       =>
       Heap
  [structural]
       

---TOSEEAGAIN!!!
  rule rhoFlds((FldK|->wkbag(<hf>Map</hf>) Heap),  (O:K |-> O':K), (FldK:K,,FldLs:List{K}))
       =>
       rhoFlds((FldK|->wkbag(<hf>mapRename(Map,O',O)</hf>) Heap),  (O:K |-> O':K), FldLs:List{K})
  [structural]
  rule rhoFlds(Heap,  (O:K |-> O':K), .List{K}) => Heap
  [structural]

---end rename


//@  \subsection{Object Creation}

/*@ ${\tt mould}\ K1 \mapsto K2\ {\tt into}\ H(F)List$ = the list of 
    $H(F)[K2/K1]$
    (used, together with ${\tt reach}$ and ${\tt firstNotIn}$, in 
    the object creation; ${\tt mould}$ is used for updating the fields 
    with the newly created object)
*/
  syntax List{K} ::= "mould" MapItem "into" List{K}
  rule mould (K1:K |-> K2:K) into (wkbag(<hf>Map:Map</hf>) ,, LKs:List{K}) 
       =>
       wkbag(<hf>Map[K2/K1]</hf>),,(mould (K1:K |-> K2:K) into LKs)
  [structural]
  rule mould (K1 |-> K2) into .List{K} => .List{K}
  [structural]

--- end object creation

--- procedure call
//@ \subsection{Procedure Call}

/*@ ${\tt setXcall}(H,L,G,F,FV) = \mathcal{R}_H(L\cup FV)\cap\mathcal{R}_H(G)$
*/
  syntax Set ::= "setXcall" "(" Map "," List{K} "," List{K} "," List{K} "," Set ")"
  rule setXcall(Heap, L, G, F, FVSet) 
       =>
       reachFromVSet((Set L) FVSet, Heap, F) nSet reachFromVSet((Set G), Heap, F)
  [structural]


/*@ ${\tt setCutPoints}(H,L,G,F) = CP(H) := 
  \{ o\in X\ |\ o\in H(L\cup FV)\cup(H(F)(X))^c \} = 
  (X\cap H(L\cup FV)) \cup (X-H(F)(X))$
*/  
  syntax Set ::= "setCutPoints" "(" Map "," List{K} "," List{K} "," List{K} ")"
  syntax Set ::= "setCPwFV" "(" Map "," List{K} "," List{K} "," List{K} "," Set ")"
  syntax Set ::= "setCP" "(" Set "," Map "," List{K} "," List{K} "," List{K} ")"

  rule setCutPoints (Heap, L, G, F) 
       =>
       setCPwFV (Heap, L, G, F, keys (Heap [undef/ F,,L,,G ]))
  [structural]

  rule setCPwFV (Heap, L, G, F, FVSet:Set)
       =>
       setCP (setXcall(Heap, L, G, F, FVSet), Heap, L, F, listK(FVSet))
  [structural]

  rule setCP (Xset:Set, Heap, L, F, FVList:List{K})
       =>
       filterX(Xset, Heap, F) (Xset nSet (Set Heap(L,,FVList)))
---  where XSet = setXcall(Heap, L, G, F)
  [structural]

*** CHECK FROM HERE filterX!!! checked: stays the same
/*@ ${\tt filterX}(X,H,F) = X-H(F)(X)$
*/
  syntax Set ::= "filterX" "(" Set "," Map "," List{K} ")"
  rule filterX (Xset, Heap, F)
       =>
       Xset -Set (flatImgOf Heap(F) on Xset)
  [structural]

/*@ ${\tt flatImgOf}\ H(F){\it list}\ {\tt on}\ {\it Set} = H(F)({\it Set})$\\
    (needed as $H(f)$ is a wrapped cell ${\sf hf}$ containing a ${\it Map}$, 
    for any $f\in F$)
*/
  syntax Set ::= "flatImgOf" List{K} "on" Set
  rule flatImgOf (wkbag(<hf>Map:Map</hf>) ,, LKs:List{K}) on Set:Set
       =>
       (imgOf Map on Set) (flatImgOf LKs on Set)
  [structural]
  rule flatImgOf .List{K} on Set => .Set
  [structural]
  
/*@ ${\tt updateCP}\ H\ {\tt with}\ c_1,..,c_l\ {\tt index}\ 
    I = H[v_I..v_{I+l-1}:=c_1..c_l]$\\
    ${\tt updateFrzCP}\ H\ {\tt with}\ c_1,..,c_l\ {\tt index}\ 
    I = H[v'_I..v'_{I+l-1},v'_{I+l}..:=c_1..c_l,\bot..]$\\
    ${\tt undefFrzCP}\ H\ {\tt start}\ I = H[v'_I..:=\bot..]$ 
    (helper for {\tt updateFrzCP})   
*/
  syntax Map ::= "updateCP" Map "with" List{K} "index" Int
  syntax Map ::= "updateFrzCP" Map "with" List{K} "index" Int
  syntax Map ::= "undefFrzCP" Map "start" Int

  rule updateCP Map with K:K,,LKs index I:Int 
       => 
       updateCP Map[K/(v-I)] with LKs index (I +Int 1)
  [structural]
  rule updateCP Map with .List{K} index I => Map
  [structural]

*** hereon modification: need to update to bot all other freezes - DONE
  rule updateFrzCP Map with K:K,,LKs index I:Int 
       => 
       updateFrzCP Map[K/frz(v-I)] with LKs index (I +Int 1)
  [structural]
  rule updateFrzCP Map with .List{K} index I => undefFrzCP Map start I
  [structural]

  eq undefFrzCP (Map frz(v-I)|->K) start I = undefFrzCP Map start I +Int 1
  eq undefFrzCP Map start I = Map [owise]
  
/*@ Computation for the ${\sf slave-k}$ cell upon procedure call 
 (${\tt processingCP}$ 
 the ${\tt set}$ of cut points, transforms the set into a list 
 with ${\tt set2list}$, 
 and passes it to ${\tt processedCP}$ which marks the end of the 
 computation on the ${\sf slave-k}$ cell for procedure call)
*/
  syntax K ::= processingCP ( Set )
  syntax K ::= processedCP ( List{K} )
  syntax List{K} ::= set2listK ( Set , List{K} )

  rule processingCP(Set:Set) => set2listK(Set, .List{K})
  [structural]
  rule set2listK(SetItem(K) Set:Set, LKs:List{K}) => set2listK(Set, (K,,LKs))
  [structural]
  rule set2listK(.Set, LKs) => processedCP(LKs) 
  [structural]

--- end procedure call

--- procedure return:
//@ \subsection{Procedure Return}

/*@ ${\tt setXret}(H_l,H_c,G,L,F) = 
      (\mathcal{R}_{H_l}(L\cup FV)- \mathcal{R}_{H_l}(G))\cap  
      \mathcal{R}_{H_c}(G\cup FV)$
*/
  syntax Set ::= "setXret" "(" Map "," Map ","  List{K} "," List{K} "," List{K} ")"

  rule setXret(Hl, Hc, G, L, F) 
       => 
       (reachFromVSet(((Set L) (keys (Hl [undef/ G,,L,,F]))), Hl, F) 
         -Set reachFromVSet(Set G, Hl, F))
       nSet reachFromVSet(((Set G)  (keys (Hc [undef/ G,,L,,F]))), Hc, F)
  [structural]


/*@ Computation for the ${\sf slave-k}$ cell upon procedure return:\\
  ${\tt processingHk}$ triggers ${\tt truceHcHl}$ which renames the 
  {\it conflicting} objects from $X = {\tt setXret}(H_l,H_c,G,L,F)$
  with the first $|X|$ positive integers not in
  $\mathcal{R}_{H_0}\cup\mathcal{R}_{H_l}(L\cup FV)$; 
  the result is passed to ${\tt processedHk}$ 
  which marks the end of the computation on the
  ${\sf slave-k}$ cell for procedure return\\
  
*/

  syntax K ::= "processingHk" "(" Map "," Map "," List{K} "," List{K} "," List{K} ")"
  syntax K ::= "processedHk" "(" Map ")"

/*@ ${\tt truceHcHl}(H_0,X,H_l,G,L,F) = \rho (H_0, x_1,..,x_k\rightarrow 
{\tt firstNotIn}\ \mathcal{R}_{H_0}\cup\mathcal{R}_{H_l}(L\cup FV)\ {\tt count}\ k)$
*/
  syntax K ::= "truceHcHl" "(" Map "," Set "," Map "," List{K} "," List{K} "," List{K} ")"

  rule processingHk (Hl,Hc,L,G,F) 
       =>
       truceHcHl(Hc[bot/L], setXret(Hl,Hc,G,L,F), Hl, G, L, F)
  [structural]


  rule truceHcHl(H0:Map, Xret:Set, Hl:Map, G:List{K}, L:List{K}, F:List{K})
       =>
       rhoList(H0, listK(Xret), (listFirstNotIn (reach(H0,F) reachFromVSet(((Set L) (keys (Hl [undef/ G,,L,,F ]))),Hl,F)) count | Xret |), G, F)
  [structural]
--- !!!CAREFUL about G here above!!!


*** news
/*@ ${\tt rhoList}(H,{\it List}_1,{\it List}_2,GLs,F) = 
     \rho(H,{\it List}_1\rightarrow {\it List}_2)$ is a helper for 
    ${\tt truceHcHl}$
*/
  syntax K ::= "rhoList" "(" Map "," List{K} "," List{K} "," List{K} "," List{K} ")"

  rule rhoList(Heap, ((O:K),,(LOs:List{K})),  ((O':K),,(LOs':List{K})), GLs, F)
       =>
       rhoList(rho(Heap, (O |-> O'), GLs, F), LOs, LOs', GLs, F)
  [structural]
  rule rhoList(Heap, .List{K}, .List{K}, GLs, F) => processedHk(Heap)
  [structural]

*** news



*** Iterative Version of Hk

/*@ The iterative version of $H_k$ (not used currently):\\
    {\tt processingHkIter}$(H_l,H_c,L,G,F) = H_k$ from the documentation\\
*/
  syntax K ::= "processingHkIter" "(" Map "," Map "," List{K} "," List{K} "," List{K} ")"

  rule processingHkIter(Hl,Hc,L,G,F)
       =>
       iterateOnXret(Hc[bot/L], setXret(Hl,Hc,G,L,F), 
          reachFromVSet(((Set L) (keys (Hl [undef/ G,,L,,F ]))),Hl,F), (G,,L), F) 
  [structural]


*** CHECK New settings FROM HERE!!!
/*@ 
    {\tt iterateOnXret}$(H_l,H_c,L,G,F) = \rho (H_i,x_i\rightarrow {\it min}\{ n\in \mathbb{N}\ |\ n\notin \mathcal{R}_{H_i} \cup \mathcal{R}_{H_l}(L\cup FV)\})$ from the documentation\\
*/
  syntax K ::= "iterateOnXret" "(" Map "," Set "," Set "," List{K} "," List{K} ")"
  rule iterateOnXret(Hi:Map, (SetItem(Xi:K) Set), ReachHlLFV:Set , GLs, F)
       =>
       iterateOnXret(Hi1, Set, ReachHlLFV, GLs, F)
  where Hi1 = rho(Hi,(Xi |-> (firstNotIn (reach(Hi,F) ReachHlLFV))), GLs, F)
  [structural]
  rule iterateOnXret(Hi, .Set, ReachHlLFV, GLs, F) => processedHk(Hi)
  [structural]

*** end Iterative Version of Hk


--- Hr = Hk[Hl(L)/L][fPrime(Hl,Hc,F,L,G)/F]
/*@ {\tt fPrime}$(H_l,H_c,F,L,G) = f'_1,...,f'_k$ from the documentation;\\
{\tt fPrimeListK}$(H_l|{F},H_c|_{F},\mathcal{R}_{H_l}(L\cup FV)-\mathcal{R}_{H_l}(G))$ is a helper for {\tt fPrime}
*/
  syntax List{K} ::= "fPrime" "(" Map "," Map "," List{K} "," List{K} "," List{K} ")"
  syntax List{K} ::= "fPrimeListK" "(" List{K} "," List{K} "," Set ")"


  rule fPrime (Hl,Hc,F,L,G)
       =>
       fPrimeListK (Hl(F), Hc(F), ReachHlLG)
--- where ReachHlLG =  (reachFromVSet((Set L),Hl,F) -Set reachFromVSet((Set G),Hl,F))
  where ReachHlLG = (reachFromVSet(((Set L) (keys (Hl [undef/ L,,G,,F ]))),Hl,F) -Set reachFromVSet((Set G),Hl,F))
  [structural]

--- Hc is actually passed as Hk in restore rule
  rule fPrimeListK((KHl:K,,LHl:List{K}), (KHc:K,,LHc:List{K}), Set)
       =>
       (updateWKBag KHc with KHl on Set),,fPrimeListK(LHl,LHc,Set)
  [structural]
  rule fPrimeListK(.List{K}, .List{K}, Set) => .List{K}
  [structural]

/*@ an {\tt update} which goes inside the structure of the wrapper {\tt wkbag}:\\
  {\tt updateWKBag} $H(f)$ {\tt with} $H(f')$ {\tt on} 
  $o_1,...,o_n = H(f)[o_1,...,o_n := H(f')(o_1),...,H(f')(o_n)]$ 
  is a helper for ${\tt fPrime}$
*/  
  syntax K ::= "updateWKBag" K "with" K "on" Set
  rule updateWKBag wkbag(<hf>MapHc:Map</hf>) with wkbag(<hf> MapHl:Map </hf>) on (SetItem(K) Set) 
       => 
       updateWKBag wkbag(<hf>MapHc[MapHl(K)/K]</hf>) with wkbag(<hf>MapHl</hf>) on Set
  [structural]
  rule updateWKBag KHc with KHl on .Set => KHc
  [structural]

---(
*** same as fPrimeListK
/*@ Same as {\tt fPrimeListK} above, while {\tt updateMap} is a helper, similar to {\tt updateWKBag} above. Not used though.
*/
  syntax List{K} ::= "fPrimeListKmould" "(" List{K} "," List{K} "," Set ")"
  rule fPrimeListKmould((wkbag(<hf>MapHl:Map</hf>),,LHl:List{K}), (wkbag(<hf>MapHc:Map</hf>),,LHc:List{K}), Set)
       =>
       wkbag(<hf>updateMap MapHc with MapHl on Set</hf>),,fPrimeListKmould(LHl,LHc,Set)
  [structural]
  rule fPrimeListKmould(.List{K}, .List{K}, Set) => .List{K}
  [structural]

  syntax Map ::= "updateMap" Map "with" Map "on" Set
  rule updateMap MapHc with MapHl on (SetItem(K) Set) 
       => 
       updateMap MapHc[MapHl(K)/K] with MapHl on Set
  [structural]
  rule updateMap MapHc with MapHl on .Set => MapHc
  [structural]
---)
--- end procedure return


******************
******************
******************
//@ Needed for safety properties

  syntax K ::= #Rexp | #Set{Tuple} | #SatConfig | #Set{Obj}

  syntax #Rexp ::= Id
  syntax #Heap ::= "map2heap" "(" Map ")"
  syntax #Bool ::= Map "|=" #Rexp
  rule (map2heap(Map)) |= R:#Rexp => (Map |= R) [structural]

  syntax #Set{Obj} ::= "obj" "(" Map ")"

  macro obj(map2heap(Map)) = obj(Map)

  rule obj(.Map) => emptyObj [structural]
  rule obj(X |-> VX Map) => VX ;SO obj(Map) [structural]
  rule obj(VX |-> VY Map) => VY ;SO obj(Map) [structural]
  rule obj(Fld |-> wkbag(<hf> M </hf>) Map) => obj(M) ;SO obj(Map) [structural]

  syntax Prop ::= #Rexp

  rule Map |= True => true [structural]
  rule Map |= le(I:Int) => size(Map) <=Int I  [structural]

  syntax #Tuple ::= "<" Map ";" #Set{Tuple} ";" #Set{Tuple} ">"
  macro < map2heap(Map) ; DST:#Set{Tuple} ; DST':#Set{Tuple} > = < Map ; DST ; DST' > 

//  ceq  < (X |-> O) H ; (O, R, X) ; DST > = < (X |-> O) H ; (O, R { X }) ; DST > if not exception(R) .
  rule < ((X |-> VX) Map) ; (`(_`,_`,_`)(VX, R:#Rexp, X)) ; DST:#Set{Tuple} >
       =>
       < ((X |-> VX) Map) ; `(_`,_`)(VX, R { X }) ; DST >
       if notBool exception(R)
       [structural]


//  eq < H ; (O, R1 + R2, A) ; DST > = < H ;  (O, R1, A) ; DST > < H ; (O, R2, A) ; DST > .
  rule < Map ; `(_`,_`,_`)(VX, R1:#Rexp ++ R2:#Rexp, A:#Alph) ; DST >
       =>
       < Map ; `(_`,_`,_`)(VX, R1, A) ; DST > ;ST < Map ; `(_`,_`,_`)(VX, R2, A) ; DST >
       [structural]
 

/*
  ceq  < (X |-> O') H ; (O, R, ! X) ; DST > = < (X |-> O) H ; (O, R { ! X }) ; DST > if not exception(R) and (O =/= O') .
*/
  rule  < X |-> VX':IntBot Map ; `(_`,_`,_`)(VX, R, ! X) ; DST >
        =>
        < (X |-> VX) Map ; `(_`,_`)(X, R { ! X }) ; DST >
        if _andBool_(notBool exception(R), (VX !=Int VX'))
       [structural]

***

//  eq  < H ; (O, R, A) ; DST > = emptyTuples [owise] .
//  eq  < Map ; `(_`,_`,_`)(VX, R, A) ; DST > => emptyTuples [owise] .

//  eq  < H ; (O, epsilon, A) ; DST > = < H ; emptyTuples ; DST > .
//  rule  < Map ; `(_`,_`,_`)(VX, epsilon, A) ; DST > => < Map ; emptyTuples ; DST >
//       [structural]

/*
  ceq  < F |-> (<hf> (O |-> O') H1 </hf>) H ; (O, R, F) ; DST > = < F |-> (<hf> (O |-> O') H1 </hf>) H ; (O', R { F }) ; DST >  if not exception(R) .
*/
  rule  < Fld |-> wkbag(<hf> (VX |-> VX') M </hf>) Map ; `(_`,_`,_`)(VX, R, Fld) ; DST >
        =>
        < Fld |-> wkbag(<hf> (VX |-> VX') M </hf>) Map ; `(_`,_`)(VX', R { Fld }) ; DST >
        if notBool exception(R)
       [structural]



  syntax Prop ::= "le" "(" Int ")" | `True | `False
  syntax #Bool ::= Map `|= Prop

  syntax Int ::= size ( Map ) 

  rule size(.) => 0 [structural]

  rule size( X |-> VX Map ) => 1 +Int size(Map)
       if (VX !=Int bot)
       [structural]  
  rule size( X |-> bot Map ) => size(Map)  [structural]
  rule size( VX |-> VY Map ) => 1 +Int size(Map)
       if (VY !=Int bot)
       [structural]  
  rule size( VX |-> bot Map ) => size(Map)  [structural]

  rule size( Fld |-> wkbag(<hf> M:Map </hf>) Map) => size(M) +Int size(Map) [structural]

  syntax K ::= "check"  | "failure"

******************
******************
******************

/*@ The actual semantic rules:
*/
  configuration <T color="purple"> 
                  <config multiplicity="*" color="yellow">
                    <master color="blue">
                      <k color="green"> .K </k>
                      <heap color="yellow"> .Map </heap>
                      <step> 0 </step>
                    </master>
                    <slave color="gray">
                      <k color="purple"> .K </k>
                    </slave>
                  </config>
                  <pgm color="magenta"> .Map </pgm>
                  <form> le(1) </form>
                  <out color="purple"> "true" </out>
                </T>

  syntax CellLabel ::= "hf"

--- rules from basics

  syntax Bag ::= "run" "(" KLabel ")"

  rule [initialisation] :
  run (KL:KLabel) => 
        <T_> 
          <config_>
            <master_>
              <k> KL(.List{K})~>main </k>
            <_/master>
          <_/config>
        <_/T> [structural]



  rule [procedure-sequentialisation] : ( Ps1:Procs Ps2:Procs ) => Ps1 ~> Ps2
  rule [processing-procedure-declaration] :
       <config_>
         <master_>
           <k> ( P:ProcId :: B:B ) => . <_/k>
         <_/master>
       <_/config>
       <pgm_> .Map => P|->B <_/pgm>

  rule [processing-variables-lists] :
  <config_>
    <master_>
       <k> (gvars: LG:Ids  lvars: LL:Ids flds: LF:Ids { Ps:Procs}) 
           => 
           Ps 
       <_/k>
       <heap> H:Map 
              => 
              H[wkbag(<hf>bot|->bot</hf>)/id2listk(LF)][bot/id2listk(_`,_(LG,LL))] 
       </heap>
     <_/master>
   <_/config>
      <pgm> .Map 
             => 
            ( gvars|->klist(id2listk(LG))
              lvars|->klist(id2listk(LL))
              flds|->klist(id2listk(LF))
            )
      </pgm>


  rule [check-true] :
    <master_>
       <k> check => . <_/k>
       <heap> H </heap>
    <_/master>
    <form> Phi:Prop </form>
    if H |= Phi
    [structural]

  rule [check-false] :
    <master_>
       <k> check => failure <_/k>
       <heap> H </heap>
    <_/master>
    <form> Phi:Prop </form>
    if notBool(H |= Phi)
    [structural]

  rule [control-sequantialisation] : B1:B;B2:B => B1~>B2

  rule [skip] : <master_>  <k> skip => . <_/k> <_/master> 

  
  rule [assignment] : 
    <master_>
       <k> X:Id := Y:Id => check <_/k>
       <heap> (H X |-> VX Y |-> VY ) => (H X |-> VY Y |-> VY )  </heap>
    <_/master>
   

  rule [assignment-special-case] :
    <master_>
       <k> X:Id:=X:Id => . <_/k>
//       <heap_> X|->_ <_/heap>
    <_/master>



  rule [control-conditional-equal] :
    <master_>
       <k> [X=Y]B:B => B <_/k>
       <heap> X|->VX:IntBot Y|->VX H </heap>
    <_/master>
---  rule <k> [X=Y]B:B => . <_/k>
---       <heap_> X|->VX:IntBot Y|->VY:IntBot <_/heap>
---  if VX !=Int VY
  rule  [conditional-equal-special-case] :
    <master_>
       <k> [X=X]B:B => B <_/k>
---       <heap_> X|->_ <_/heap>
    <_/master>

  rule  [control-conditional-notEqual] :
    <master_>
       <k> [X/=Y]B:B => B <_/k>
       <heap_> X|->VX:IntBot Y|->VY:IntBot <_/heap>
    <_/master>
  if VX !=Int VY
---  rule <k> [X/=Y]B:B => . <_/k>
---       <heap_> X|->V:IntBot Y|->V <_/heap>

/*
  rule [control-nondet-choice-1] : <master_> <k> B1+B2 => B1 <_/k> <_/master>
  rule [control-nondet-choice-2] : <master_> <k> B1+B2 => B2 <_/k> <_/master>
*/

  rule <config>
         <master>
           <k> B1+B2 ~> K:K </k>
           CFG':Bag
         </master>
         CFG:Bag
       </config>
       =>
       <config>
         <master>
           <k> B1 ~> K </k>
           CFG'
         </master>
         CFG
       </config>
       <config>
         <master>
           <k> B2 ~> K </k>
           CFG'
         </master>
         CFG
       </config>


--- rules from basics

  rule [object-creation] :
    <master_>
       <k> X:Id :=new => check <_/k>
       <heap> H:Map 
              => 
              H[ONew/X][(mould (ONew|->bot) into H(F))/F]
       </heap>
    <_/master>
       <pgm_> flds |-> klist(F:List{K}) <_/pgm>
  where ONew = (firstNotIn reach(H, F))


  rule [assignment-field-rhs] :
    <master_>
       <k> _:=_(X:Id, _._(Y:Id ,Fld:Id)) => check <_/k>
       <heap> X |-> (VX => V) Y|->VY:IntBot 
              Fld |-> wkbag(<hf> VY|->V:IntBot HF:Map </hf>)
              H
       </heap> 
    <_/master>

  rule  [assignment-field-rhs-special-case] :
    <master_>
       <k> _:=_(X:Id, _._(X:Id ,Fld:Id)) => check <_/k>
       <heap> X |-> (VX:IntBot => V) 
              Fld |-> wkbag(<hf> VX |-> V:IntBot HF </hf>)
              H
       </heap> 
    <_/master>


 rule  [assignment-field-lhs] :
   <master_>
      <k> _:=_( _._(X:Id , Fld:Id), Y:Id) => check <_/k>
---      <heap_> Fld|-> wkbag(<hf>M:Map => M[VY/VX]</hf>) 
      <heap> Fld|-> wkbag(<hf> VX |-> (V => VY) HF </hf>) 
             X|->VX:IntBot Y|->VY:IntBot 
             H
      </heap> 
   <_/master>

 rule  [assignment-field-lhs-special-case] :
   <master_>
      <k> ( X:Id . Fld:Id := X:Id) => check <_/k>
---      <heap_> Fld|-> wkbag(<hf>M:Map => M[VX/VX]</hf>) 
      <heap> Fld|-> wkbag(<hf> VX |-> (V => VX) HF </hf>) 
             X|->VX:IntBot 
             H
      </heap>
   <_/master>

  rule [procedure-call-initialisation] : 
      <config>
        <master_>
          <k> P:ProcId <_/k> 
          <heap> H:Map </heap>
          <step> N => N +Int 1 </step>
        <_/master> 
        <slave><k>.=>processingCP(setCutPoints(H,L,G,F))</k></slave>
      <_/config>
       <pgm_> lvars|->klist(L:List{K}) 
              gvars|->klist(G:List{K}) 
              flds|->klist(F:List{K})
              P|->B:B 
       <_/pgm>
     if N <Int 10
---  where CP = listK(setCutPoints(H,L,G,F))
     [structural large]
  
  rule  [procedure-call-finalisation] :
      <config_>
       <master_>
         <k> P => check~>B~>restore(H) <_/k>
---!!!CHECK WITH JURRIAAN: B~>restore(updateCP H with CP index 1) <_/k>
         <heap> H:Map 
                => 
                (updateFrzCP H with CP index 1)[bot/L]
         </heap>
       <_/master> @latex("\\kBR")
       <slave><k> processedCP(CP:List{K})=>. </k></slave>
      <_/config>
       <pgm_> lvars|->klist(L:List{K}) 
              gvars|->klist(G:List{K}) 
              flds|->klist(F:List{K})
              P |-> B:B 
       <_/pgm>

---  where CP = listK(setCutPoints(H,L,G,F))
  [large]



  rule  [procedure-return-initialisation] :
    <config_>
      <master_>
        <k> restore(Hl:Map) <_/k>
        <heap> Hc:Map </heap>
      <_/master> @latex("\\kBR")
      <slave><k> .=>processingHk(Hl,Hc,L,G,F)</k></slave>
    <_/config>
       <pgm_> lvars|->klist(L:List{K}) 
              gvars|->klist(G:List{K}) 
              flds|->klist(F:List{K})
       <_/pgm>
  [structural large]
      
  rule  [procedure-return-finalisation] :
    <config_>
      <master_>
        <k> restore(Hl:Map) => check <_/k>
        <heap> Hc
               => 
               (Hk[undef/ listK(keys (Hk[undef/ L,,G,,F]))])[Hl(L)/L]
                  [Hl(listK(keys (Hl[undef/ L,,G,,F ])))/listK(keys (Hl[undef/ L,,G,,F]))]
                     [fPrime(Hl,Hk,F,L,G)/F] --- = Hr
        </heap>
      <_/master> @latex("\\kBR")
      <slave><k> processedHk(Hk:Map)=>. </k></slave>
    <_/config>
       <pgm_> lvars|->klist(L:List{K}) 
              gvars|->klist(G:List{K}) 
              flds|->klist(F:List{K})
       <_/pgm>
  [large]


end module


