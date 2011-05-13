/*
*  The code implements the contents of the paper:
*  "Symbolic Execution of Unbounded Object Creation"
*  by Juriaan Rot, Frank de Boer, Marcello Bonsangue
*  (LIACS - Leiden University, and CWI)
*  The focus of this file is on Section 6 in the paper.
*/

require silok-programs
// require silok-syntax

kmod SILOK-SYMBOLIC-SEMANTICS 
is including SILOK-SYNTAX + K + PL-INT + PL-ID + PL-EXT-BOOL + SILOK-PROGRAMS


// The same structure for K as in silok-basics with the addition of the St sort
// for the current content of the state cell - now it is a formula not a mapping. 
  syntax K ::= B | restore ( Map ) | lvars | gvars 
  	       | Procs | Pgm | St | IdInt | ListId
// Smb is used for evaluating the entailment
  syntax Builtins ::= Smb
  syntax KResult ::= Int | Id

  syntax K ::= wklist ( List{K} )


// listK transforms the list of variables ListId into a List{K}, 
// a structure fit for Map, which is the way we store the program
  syntax List{K} ::= listK ( ListId )
  rule listK(Id:Id,LI:ListId) => Id ,, listK(LI) 
       if LI =/=Bool .ListId [structural]
  rule listK(Id) => Id [structural]
  rule listK(.ListId) => .List{K} [structural]


// The background for the entailment, basically defining a state formula as in the paper
// with features as commutativity for equality, here denoted as ==Smb,
// and commutativity and associativity for conjunction, here denoted as andSmb
  syntax SmbAtom ::= IdBtm ==Smb IdBtm [comm prec 40]

  syntax Smb ::= SmbAtom  
		 | Smb andSmb Smb [comm assoc id: epsilon prec 41]
		 | epsilon

// St defines basically a frozen form of the state formula 
// (without the commutativity features for equality and conjunction)
// We use this frozen form in the state cell, while the Smb form is used for
// reasoning about the entailment.
  syntax St ::= IdBtm ==St IdBtm [prec 40] 
                | `.St
                | St andSt St [assoc id: .St prec 41] 

// st2smb takes the frozen formula St and transforms it into a Symbolic formula,
// for entailment reasoning. 
  syntax Smb ::= st2smb `( St `)
  eq st2smb (.St) = epsilon
  eq st2smb ( XI ==St YI andSt St ) = XI ==Smb YI andSmb st2smb(St)


// The fresh variables are produced in the fashion of single static assignment
// i.e. to each variable we associate a number (current incarnation) and this
// number is attached to the variable name like this: 
// VarName - CurrentIncarnationValue
// Each time a certain variable is the left-handside of an assignment, the variable
// receives a new current incarnation which is updated according to the assignment
// (this method is preferred to the substitution in the formula, only for efficiency
// reasons, as substitution is linear in the size of the formula, while the current 
// approach takes constant time). However, from the point of view of the produced formula,
// the approach in the paper is equivalent to the one in the implementation.   
  syntax IdBtm ::= IdInt | btm
  syntax IdInt ::= K `- Int [prec 30]
  syntax Id ::= fst IdInt [prec 35]
  syntax Int ::= snd IdInt [prec 35]
  eq fst Id:Id - I:Int = Id
  eq snd Id - I = I

// Atom inSmb Formula checks if an Atom is a conjunct in the conjunctive Formula.
  syntax Bool ::= SmbAtom inSmb Smb
  eq (XI ==Smb YI) inSmb (XI ==Smb YI andSmb Phi) = true
  eq (XI ==Smb YI) inSmb Phi = false [owise]


// prove Atom from Formula constructs the transitive closure of the Formula
// and stops when the Atom was already added to the partial transitive closure
// of the Formula, with the first equation, or when we cannot add any new atoms
// to the transitive closure of the Formula, meaning that we've reached the
// final form of the transitive closure without finding the Atom we're looking for,
// with the third equation.
/* 
* Obs: preferable to use fair-rewrite to run the programs, because the rewrite would
*      overlook the first equation too often, and try to match the second one modulo AC, 
*      without too much success. Note that in the condition of the second equation
*      we check only that the Atom is not equal to the newly introduced atom,
*      produced by the application of the transitivity rule. 
*/
  syntax Bool ::= prove SmbAtom from Smb
  eq  prove (XI:IdBtm ==Smb YI:IdBtm) from (XI ==Smb YI andSmb Phi:Smb) = true
  ceq prove (XI ==Smb YI) from 
        (Phi:Smb andSmb XI1:IdBtm ==Smb XI2:IdBtm andSmb XI2 ==Smb XI3:IdBtm)
      =
      prove (XI ==Smb YI) from 
        (XI1 ==Smb XI3 andSmb XI1 ==Smb XI2 andSmb Phi andSmb XI2 ==Smb XI3) 
  if notBool ((XI ==Smb YI) inSmb  (XI1 ==Smb XI3))
     and-then
     notBool ((XI1 ==Smb XI3) inSmb  (Phi andSmb XI1 ==Smb XI2 andSmb XI2 ==Smb XI3))
  eq prove (XI ==Smb YI) from Phi = false [owise]


// \=Smb(Formula, Atom) checks the entailment relation by first trying to find the
// Atom in the formula, and if this does not succeed, prove Atom from the partially
// constructed transitive closure of the formula, as explained above for
// prove Atom from Formula.   
  syntax Bool ::= \=Smb ( Smb , SmbAtom ) [prec 45]
  eq \=Smb (Phi, (XI:IdBtm ==Smb YI:IdBtm)) 
     = 
     ((XI ==Smb YI) inSmb Phi)  or-else (prove (XI ==Smb YI) from Phi) 

// Formula X=Smb Atom  checks if the Atom cannot be entailed from the Formula.
  syntax Bool ::= Smb `X=Smb SmbAtom [prec 45]
  eq Phi X=Smb (XI ==Smb YI) = notBool \=Smb(Phi, (XI ==Smb YI))


---(
// For some unexpected reason, at some level in the transformation - probably
// at the level of the back-end transformations -
// the kompile is not able to parse this particular infix form of the \=Smb.
// This is why we are compelled to use the less elegant prefixed form as above. 
  syntax Bool ::= Smb `\=Smb SmbAtom [prec 45 gather (e e)]
  eq Phi \=Smb (XI:IdBtm ==Smb YI:IdBtm)
     = 
     ((XI ==Smb YI) inSmb Phi)  or-else (prove (XI ==Smb YI) from Phi) 

  syntax Bool ::= Smb `X=Smb SmbAtom [prec 45]
  eq Phi X=Smb (XI ==Smb YI) = notBool Phi \=Smb (XI ==Smb YI)
---)

// andStV0EqBtm List \equiv /\_{X \in List} ( X_0 = btm ) 
// used for the setup of the initial state formula.
// andStV0EqBtm List takes all variables from the List, associates the incarnation
// number 0, and equals these incarnations to btm.
  syntax St ::= andStV0EqBtm List{K}
  eq andStV0EqBtm .List{K} = .St 
  eq andStV0EqBtm (K:K ,, Ks:List{K}) = K - 0 ==St btm andSt andStV0EqBtm Ks

// State andStList List - CurrentIncarnation =btm 
//  \equiv State /\_{X \in List} X - (1 + CurrentIncarnation(X)) = btm
// used to update the local variables upon a procedure call 
  syntax St ::= St andStList List{K} `- Map `=btm
  eq St:St andStList .List{K} - Map:Map =btm = St
  eq St andStList K:K,, L:List{K} - ( K |-> I Map ) =btm 
     = 
     (St andStList L - (K |-> I Map) =btm) andSt  (K - (I +Int 1) ==St btm)
  eq St andStList K:K,,L - Map =btm 
     = 
     (St andStList L - Map =btm) andSt  (K - 0 ==St btm)
  [owise]  


// inc List from Map = Map[(Map(X) + 1) /X], \forall X in List
// used to produce fresh incarnations
// inc List from Map increments the values in the Map associated to the variables 
// from the List 
  syntax Map ::= inc List{K} from Map
  eq inc .List{K} from Map = Map
  eq inc K,,L from (K |-> I Map) = inc L from (K |-> (I +Int 1) Map)
  eq inc K,,L from Map = inc L from (K |-> 0 Map) [owise]


// State [Incarnation1, Incarnation2, List] \equiv
// State /\_{X \in List} ( X - Incarnation1(X) =  X - Incarnation2(X) )
  syntax St ::= St `[ Map `, Map `, List{K} `]
  eq St:St [ Map1:Map, Map2:Map, .List{K} ] = St
  eq St [ (K |-> I1:Int Map1) , (K |-> I2:Int Map2) , K,,L ] 
     = (St andSt K - (I1 +Int 1) ==St K - I2)  
       [ (K |-> I1 Map1) , (K |-> I2 Map2) , L ]
  eq St [ Map1, Map2, L ] = St [owise] 



  configuration <T> 
                  <k> .K </k>
                  <state> .K </state>
		  <pgm> .Map </pgm>
		  <ci> .Map </ci>
                </T>

  syntax Bag ::= run ( KLabel )
  rule run (KL:KLabel) => 
       <T_> 
       	   <k> KL(.List{K})~>main </k>
	<_/T> [structural]



// At the start of the program execution, all global variables LG,
// are mapped to btm.
  rule <k> (gvars: LG:ListId  lvars: LL:ListId { Ps:Procs}) => Ps <_/k>
       <state> . => andStV0EqBtm listK(LG) </state>
       <ci> S:Map => S[0/listK(LG)] </ci>
       <pgm> .Map => ( gvars|->wklist(listK(LG)) lvars|->wklist(listK(LL)))</pgm>

// The processing of the procedure declaration.
  rule ( Ps1:Procs Ps2:Procs ) => Ps1 ~> Ps2
  rule <k> ( P:ProcId :: B:B ) => . <_/k>
       <pgm_> .Map => P|->B <_/pgm>

// The processing of composition.
  rule B1:B;B2:B => B1~>B2  
// The rules for the nondeterministic choice.
  rule <k> B1+B2 => B1 <_/k>
  rule <k> B1+B2 => B2 <_/k>


// Upon an assignment the current incarnation of the left-handside variable X
// is incremented (according to the static single assignment technique)
// while the state cell content is updated with the equality
// X - NewIncarnation = Y - CurrentIncarnation
  rule <k> X:Id:=Y:Id => . <_/k>
       <state> Sigma:St => Sigma andSt X-(I +Int 1) ==St Y-J </state>
       <ci_> X |-> (I:Int => I +Int 1) Y |-> J:Int <_/ci>

// Upon an assignment with new the current incarnation of the 
// left-handside variable X is incremented 
// (according to the static single assignment technique)
  rule <k> X:Id :=new => . <_/k>
       <ci_> X|->(I => I +Int 1) <_/ci>

// The equality condition X=Y need to be satisfied in the state cell
// The entailment satisfaction is stated in the if condition
// as SymbolicFormOf State \=Smb (X_CurrentIncarnation(X) = Y_CurrentIncarnation(Y))
  rule <k> [X=Y]B:B => B <_/k>
       <state> Sigma </state>
       <ci_> X|->I Y|->J <_/ci>
  if \=Smb (st2smb(Sigma), (X-I ==Smb Y-J))
---  if st2smb(Sigma) \=Smb (X-I ==Smb Y-J)

// The inequality condition is implemented according to the paper, as the
// negation of the entailment for equality.
  rule <k> [X/=Y]B:B => B <_/k>
       <state> Sigma </state>
       <ci_> X|->I Y|->J <_/ci>
  if st2smb(Sigma) X=Smb  (X-I ==Smb Y-J)
 

// At the beginning of a procedure call, all local variables are given
// a new incarnation (with inc LV from CI), and the state is updated
// with the equalities stating 
/* /\_{LocalVar \in L} (LocalVar - NewIncarnation = btm) */
  rule <k> P:ProcId => B~>restore(CI) <_/k>
       <state> Sigma:St => Sigma andStList LV - CI =btm </state> 
       <ci> CI:Map => (inc LV from CI) </ci>
       <pgm_> lvars|->wklist(LV:List{K}) P|->B:B <_/pgm>


// Upon exit from a procedure call we come with a fresh incarnation for 
// all local variables which are equal to the current incarnations 
// before the procedure call, retrieved from the restore(...):
/* 
* /\_{LocalVar \in LV} 
*    ( LocalVar - NewIncarnation(LocalVar) 
*      = 
*      LocalVar - RestoreIncarnation(LocalVar)
*    )
*/ 
  rule <k> restore(CI':Map) => . <_/k>
       <state> Sigma => Sigma[CI, CI', LV] </state> 
       <ci> CI => (inc LV from CI) </ci>
       <pgm_> lvars|->wklist(LV:List{K}) <_/pgm>


endkm
