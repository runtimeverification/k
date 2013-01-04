require "builtins/symbolic-k.k"
//require "builtins/fol.k"



/*!
\setlength{\parindent}{1em}
\title{PEQ (Program Equivalence)}
\author{Dorel Lucanu (\texttt{dlucanu@info.uaic.ro}) and Vlad Rusu (Vlad.Rusu@inria.fr)}
\organization{"Alexandru Ioan Cuza" University of Iasi, INRIA Lille}
*/

//@ \section{Symbolic Maps}

module MAP-SYMBOLIC
//  imports FOL

  syntax Bool ::= K "isNotModifiedBy" K [function]

  rule X:Int isNotModifiedBy S:K => true  [anywhere]
  rule X:Bool isNotModifiedBy S:K => true [anywhere]
  rule X:K isNotModifiedBy S:K => true when isSymbolicAExp(X) [anywhere]

  syntax Map ::= "followup" "(" K "," Map "," Bool ")"
  rule isSymbolicMap(followup(S:K, M:Map, F:Bool)) => true [anywhere]

  rule followup(S:K, (X:K |-> V:K M:Map), F:Bool) 
       =>
       X |-> V followup(S, M, F)
       when (F impliesBool (X isNotModifiedBy S))
       [anywhere]

  rule followup(S:K, (X:K |-> V:Int M:Map), F:Bool) 
       =>
       X |-> V' followup(S, M, F)
       when ((F impliesBool (X isNotModifiedBy S)) =/=K true)
       andBool fresh(V':Int)
       [anywhere] 

  rule followup(S:K, (X:K |-> V:Bool M:Map), F:Bool) 
       =>
       X |-> V' followup(S, M, F)
       when ((F impliesBool (X isNotModifiedBy S)) =/=K true)
       andBool fresh(V':Bool)
       [anywhere]

// temporary solution until the correct sorting of #symMap() is solved 

  syntax Map ::= "#symbMap" "(" Id ")"
  rule isSymbolicMap(#symbMap(X:Id)) => true [anywhere]

  //@ Extend keys()
  rule keys ((followup(S:K, M:Map, F:Bool) => .) _) [structural]
  rule keys ((#symbMap(_) => .) _) [structural]

  //@ Lookup
  syntax K ::= "lookup" "(" K "," Map ")" [function]
  rule [lookup] :  lookup(X:K, (_ X |-> I:Int _)) => I

  rule [lookup] :
       lookup(X:K, followup(SS:K, Rho:Map, F)) 
        => 
        lookup(X, Rho)
        when isSymbolicStmt(SS)
        andBool F impliesBool (X isNotModifiedBy SS) // to be revised

  rule [lookup] :
       lookup(X:K, followup(SS:K, Rho:Map, F) Rho':Map) 
       => 
       lookup(X, Rho)
       when isSymbolicStmt(SS)
       andBool F impliesBool (X isNotModifiedBy SS)
       andBool notBool(X in keys(Rho')) // to be revised

  //@ Update
  syntax Map ::= "update" "(" Map "," K "," K ")" [function]

  rule [update]:
       update((M:Map X:K |-> _), X, V:K) => (M X |-> V)

  rule [update]:
       update(M:Map, X:K, V:K) => (M X |-> V)
       when notBool(X in keys(M))

endmodule


//@ \section{Syntax}

module IMP-SYNTAX
  imports MAP-SYMBOLIC

/*@
  This is the syntax of IMP, where we added the multiplication operator, the
  "for" statement,  and the  labeled statements.
  The statement \texttt{for} is added just for proving its equivalence 
  with its simulation with while. The semantics of \texttt{for} is given
  in a similar way to that of while.
*/
  
  syntax AExp ::= Int | Id
  				| AExp "/" AExp [left, strict]
  				| AExp "*" AExp [left, strict]
  				> AExp "+" AExp [left, strict]
  				| "(" AExp ")"  [bracket]

  syntax BExp ::= Bool
  				| AExp "<=" AExp  [seqstrict]
  				| "not" BExp      [strict]
  				> BExp "and" BExp [left, strict(1)]
  				| "(" BExp ")"    [bracket]

  syntax Stmt ::= "skip"
  				| Id ":=" AExp   [strict(2)]
  				| "if" BExp "then" Stmt "else" Stmt [strict(1)]
  				| "while" BExp "do" Stmt
                                | "for" Id "from" AExp "to" AExp "do" Stmt
                                  [strict(2, 3)] 
                                | Id ":" Stmt
  				> Stmt ";" Stmt   [left]
  				| "(" Stmt ")"    [bracket]

  syntax Pgm ::= "var" Ids ";" Stmt
  syntax Ids ::= List{Id, ","}

/*@
  The following syntax is specific to the program equivalence.
  The "observers' are the program variables used to define the observational
  equivalence. Two configurations are observational equivalence iff each
  variable observers has the same value in both configurations.
*/


  syntax Id ::= "allObs"

  syntax InitVal ::= Id "->" Int | "SymMap" "(" Id ")"
  syntax InitVals ::= List{InitVal,","}

  syntax EqvPgm ::= "<k>" Stmt "</k>"
                    "<env>" InitVals "</env>"
                    "~" 
                    "<k>" Stmt "</k>"
                    "<env>" InitVals "</env>"
                    "if" BExp
                    "using" "observers:" Ids ";"

  syntax Start ::= EqvPgm  

/*@
  The following expressions are used in conditions.
  If it is included in the definition of the language, then its declaration
  here is no longer necessary.
*/

  syntax BExp ::= AExp "==" AExp  [strict]

  //@ get if no effect
  syntax Bool ::= "occurs" "(" Id "," Stmt ")"

  rule notBool occurs(X:Id, S:Stmt) => (X  isNotModifiedBy S) [anywhere]  //trick

  /*@
    Extending with symbolic values:
   */

  syntax Stmt ::= "#symStmt" "(" Id ")"  [onlyLabel, klabel(#symStmt)]

  syntax AExp ::= "#symAExp" "(" Id ")"  [onlyLabel, klabel(#symAExp)]

//  syntax Map ::= "#symMap" "(" Id ")" [onlyLabel, klabel(#symMap)]

  syntax Int ::= "#symInt" "(" Id ")" [onlyLabel, klabel(#symInt)]

endmodule

//@ \section{Semantics}

module PEQ
  imports IMP-SYNTAX


/*@
  A configuration is a multiset of goals. Each goal consists of an
  equivalence formula. The patterns are stored into a \texttt{config}
  cell and the condition in the \texttt{condition} cell.
  The cell \texttt{hypos} is for storing the hypotheses met during
  the proving process. It has a structure similar to that of goals, but
  where the names of cells are changed in order to forbid the rules firing
  for hypotheses, in this way the hypotheses are kept unchanged. 
  The cell \texttt{observers} stores the list of the observer variables.
*/

  configuration <T color="yellow"> 
                  <goals> 
                    <goal multiplicity="*">
                      <config multiplicity="*">
                        <k color="green"> $PGM:EqvPgm  </k>
                        <env color="red"> .Map </env>
                      </config>
                      <condition> true </condition>
                    </goal>
                  </goals>
                  <hypos>
                    <hypo multiplicity="*">
                      <patt1>
                        <k1 color="green"> .K  </k1>
                        <env1 color="red"> .Map </env1>
                      </patt1>
                      <patt2>
                        <k2 color="green"> .K  </k2>
                        <env2 color="red"> .Map </env2>
                      </patt2>
                      <condition> true </condition>
                    </hypo>
                  </hypos>
                  <observers> .List </observers> 
//                  <nextSymVar> 0 </nextSymVar>
                </T>

/*@
  The values are defined as for the original IMP, but note that now Int includes
  the symbolic integer expressions. Remember that the predicate \texttt{isBool} 
  is not extended to symbolic boolean expressions. So, the only boolean values 
  remain \texttt{true} and \texttt{false}.
*/

  syntax KResult ::= Int | #Bool

/*@
  We use a new syntactic construct that help us to store hypotheses. The basic
  idea is to add the hypotheses in a controlled way. For instance, we may add
  hypothesis only when on the top in the two k cells we have  statement with
  the same label (the label is a kind of "rendevous" synchronisarion). 
*/

  syntax K ::= "storeHypo" "(" Id "," K ")"

/*@
  The semantics of the expressions remains unchanged, excepting the memory 
  lookup and the memory update; these will be explained later.
*/

  rule [addition] : I1:Int + I2:Int => I1 +Int I2 
  rule [multiplication] : I1:Int * I2:Int => I1 *Int I2 
  rule [division] : I1:Int / I2:Int => I1 /Int I2 when I2 =/=K 0

  rule [leq] : I1:Int <= I2:Int => I1 <=Int I2
  rule [not] : not T:Bool => notBool T
  rule [and-true] : true and B:BExp => B
  rule [and-false]: false and B:BExp => false

  rule [program-no-vars]: <k> var .Ids ; S:Stmt => S ...</k> [structural]


  rule [program-still-vars]:
           <k> var X:Id, Xs:Ids; S:Stmt => var Xs; S ...</k>
          <env> Rho:Map (. => X |-> 0) </env> when notBool(X in keys(Rho))

/*@ 
  Equality of ints we additionally added:
*/

  rule [eq] : I1:Int == I2:Int => I1 ==Int I2

/*@
  The semantics for the initial statements remain unchanged, too. 
  However, most of the rules are annotated as transitions for tracing reasons.
*/

  rule [skip] : skip => .
       [structural]

  rule [sequential] : S1;S2 => S1 ~> S2 [structural]

  rule [if-true] : if true  then S:Stmt else _ => S
//       [transition]

  rule [if-false]: if false then _ else S:Stmt => S
//       [transition]

  rule [while] :
          while B:BExp do S:Stmt 
          => 
          if B then S ; while B do S else skip
//       [transition]

  rule [for]:  
       for I:Id from A1:Int to A2:Int do S:Stmt
       => 
       I := A1;
       if (I <= A2) then (S; for I from (A1 + 1) to A2  do S)
                    else skip
       [transition] 


/*@ \subsection{Labelled statements}
  We first extend the contextual declarations (derived from the strictness
  attribute) to the labelled transitions.
*/

  context _ : for _ from HOLE to _ do _
  context _ : for _ from_ to HOLE do _
  context _ : if HOLE then _ else _
  context _ : _ := HOLE 

/*@
  The labelled recursive statements have a special semantics because
  the label must be propagated. Therefore we need a boolean function
  that discriminate between recursive and non-recursive statements.
*/

  syntax Boolean ::= "isRecursive" "(" Stmt ")" [function]
  rule isRecursive(while B:BExp do S:Stmt) => true
  rule isRecursive(for I:Id from A1:AExp to A2:AExp do S:Stmt) => true


/*@
  For the non-recursive statements, the labels are translated into 
  synchronyzing construct. Naturally, for these cases only the label
  is required for the synchronization. We prefer to save the whole
  content of the cell \texttt{k} as argument of the synchronyzing
*/

  rule <k>
          ( L:Id : S:Stmt
            =>
            storeHypo(L, S ~> K) ~> S
          ) ~> K:K 
       </k>
       when isRecursive (S) =/=K true
       [transition]

/*@
  The two labeled recursive statements have a special semantics due to the
  label  propagation.
*/

  rule [while] :
       <k>
          L:Id : while B:BExp do S:Stmt ~> K:K
          => 
          storeHypo(L, while B do S ~> K) ~>
          if B then S ; L : while B do S else skip
          ~> K
       </k> 
       [transition]

  rule [for]:  
        <k> 
          L:Id : for I:Id from A1:Int to A2:Int do S:Stmt ~> K:K
           => 
          storeHypo(L, for I from A1 to A2 do S ~> K) ~>
          I := A1;
          if (I <= A2) then (S; L : for I from (A1 + 1) to A2  do S)
                       else skip
          ~> K
        </k> 
       [transition]

/*@
  Semantics of the symbolic statements:
*/


  rule [symbolic-stmt] : 
       <k> #symStmt(SS:K) => .  ...</k>
       <env> M:Map => followup(#symStmt(SS), M, F) </env>
       <condition> F:Bool </condition>
//       when isSymbolicStmt(SS)
       [transition] 


  rule [symbolic-aexp] :
       <k> #symAExp(XS:K) => lookup(#symAExp(XS), Rho) ...</k>
       <env> Rho </env>
       when #symAExp(XS) in keys(Rho)
       [transition]

  rule [symbolic-aexp] : 
       <config>... 
         <k> #symAExp(XS:K) =>  VS ...</k>
         <env> Rho:Map => update(Rho, #symAExp(XS), VS) </env>
       ...</config>
       <config>...
         <env> Rho':Map => update(Rho', #symAExp(XS), VS) </env>
       ...</config>
       when (notBool #symAExp(XS) in keys(Rho)) andBool fresh(VS:Int)
       [transition] 

/*@
  The memory lookup rule is changed because now the memory can be a 
  symbolic one obtained after a the execution of a symbolic statement.
*/


  rule [lookup] : 
       <k> X:Id =>  lookup(X, Rho) ...</k>
       <env> Rho:Map </env> 
       [transition] 

/*@
  The semantics of the assignment is modified because of the symbolic  
  statements.
*/

  rule [assignment]:
       <k> X:Id := I:Int => . ...</k>
       <env> Rho:Map => update(Rho, X, I) </env>
       [transition]


/*@
  additional rules that conservatively extend the definition
*/

  rule [sumb-boolean] :
       <k>
          B:K
          =>
          checkSat(filter(F andBool B)) ~> checkSat(filter(F andBool notBool B)) ~> B
       ...</k>
       <env> Rho:Map </env>
       <condition> F:K </condition>
       when isSymbolicBool(B) andBool notBool(B in keys(Rho))
       [transition]

  rule [derive-with-case-analysis]:
       <goal>
         <config>
           <k> "sat" ~> "sat" ~> B:K ~> K1:K </k>
           <env> Rho1:Map  </env>
         </config>
         <condition> F:K </condition>
         C:Bag
       </goal>
       =>
       <goal>
         <config>
           <k> storeSyns(F, B, true) ~> true ~> K1 </k>
           <env> Rho1:Map (B |-> true) </env>
         </config>
         <condition> F andBool B  </condition>
         C
       </goal>
       <goal>
         <config>
           <k> storeSyns(F, B, false) ~> false ~> K1 </k>
           <env> Rho1:Map (B |-> false) </env>
         </config>
         <condition> F andBool notBool (B) </condition>
         C
       </goal>
       when isSymbolicBool(B) andBool notBool(B in keys(Rho1))
       [transition]

  // the other two cases

  rule [sym-bool-red-to-true] :
       "sat" ~> "unsat" ~> B:K => true  // F impliesBool B
       when isSymbolicBool(B) 
       [transition]

  rule [sym-bool-red-to-false] :
       "unsat" ~> "sat" ~> B:K => false // F impliesBool notBool B
       when isSymbolicBool(B) 
       [transition]

/*@
  When an existing elementary symbolic boolean expression has to be evaluated,
  its value is read the cell \texttt{env}.
*/

  rule <k> B:K => V ...</k>
       <env>... B |-> V:Bool ...</env>
       when isSymbolicBool(B) 

/*@
  The following rules remove an inconsistent formula, where the
  condition is false. Note that the stored symbolic boolean expressions
  are parts of the condition.
*/

  rule <goal>...
         <env>... B:K |-> true B |-> false ...</env>
       ...</goal>
       =>
       .
       when isSymbolicBool(B) 

  rule <goal>...
         <env>... B:K |-> true ...</env>
         <env>... B |-> false ...</env>
       ...</goal>
       =>
       .
       when isSymbolicBool(B) 

/*@
  The folowing rule "borrows" the value of a elementary boolean expression
  from the pairing configuration. Since these expressions includes symbolic
  values whose scopes are the entire formula, this rule is sound.
  Note also that only sysnonims are usually stored only in one environment.
*/

  rule <goal>...
         <config>...
           <k> B:K => V ...</k>
           <env> Rho:Map </env>
         ...</config>
         <config>...
           <env>... B |-> V:Bool ...</env>
         ...</config>
       ...</goal>
       when isSymbolicBool(B) andBool notBool (B in keys(Rho))

  /*@
    Store the elementary symbolic boolean expressions obtained as
    "synonims" of the already stored ones due to the path formula 
  */

  syntax K ::= "storeSyns" "(" K "," K "," Bool ")"

  rule storeSyns(F1:K andBool F2:K, B:K, V:Bool) 
       =>
       storeSyns(F1, B, V) ~> storeSyns(F2, B, V)

  rule <k> storeSyns(I1:Int ==Int I2:Int, B:K, V:Bool) => . ...</k>
       <env>... . => (B[I1/I2] |-> V) ...</env>
       when B[I1/I2] =/=K B

  rule <k> storeSyns(I1:Int ==Int I2:Int, B:K, V:Bool) => . ...</k>
       <env>... . => (B[I2/I1] |-> V) ...</env>
       when B[I2/I1] =/=K B

  rule <k> storeSyns(I1:Int ==Int I2:Int, B:K, V:Bool) => . ...</k>
       when (B[I1/I2] ==K B) andBool (B[I2/I1] ==K B)

  rule storeSyns(X:Id isNotModifiedBy S:Stmt, B:K, V:Bool) => .

  rule <k> storeSyns(I1:Int <=Int I2:Int, B:K, V:Bool) => . ...</k>

  rule <k> storeSyns(notBool(F:K), B:K, V:Bool) => . ...</k>

/*@
  The special bag \texttt{success} is used for removing goals.
*/

  syntax Bag ::= "success"

  rule success success => success 

//  rule <T> <goals> success </goals> B:Bag </T> => success

/*@
  The next rule implements the basic entailment relation. The current version
  is incomplete because the formula is ignored (we tested only examples where
  the formula is true. We have to elaborate the implementation of the basic
  entailment.
*/

  rule [obs-equality] :
       (<goal>
         <config>
           <k> K:K </k>
           <env> Env:Map </env>
         </config>
         <config>
           <k> K </k>
           <env> Env':Map </env>
         </config>
         <condition> F:K </condition>
       </goal>
       =>
       success)
       <observers> Obs:List </observers>
       when eqObs(<env> Env </env> 
                  <env> Env' </env>
                  <observers> Obs </observers>, F)
            ==K true
       [transition]


/*@
  The observational equivalence relation is defined by checking the equality of
  the observer variables in the two configurations (see how \texttt{eqObs} is 
  called.
*/

  syntax Bool ::= "eqObs" "(" Bag "," K ")" [function]

  rule eqObs(<env> _ </env>
             <env> _ </env>
             <observers> .List </observers>, F:K)
       =>
       true


  rule eqObs(<env> Env1:Map </env>
             <env> Env2:Map </env>
             <observers> ListItem(allObs) </observers>, F:K)
       =>
       eqEnv(Env1, Env2)


  rule eqObs( <env>... X:Id |-> V1:K ...</env>
              <env>... X:Id |-> V2:K ...</env>
              <observers> ListItem(X) => . ...</observers>, F:K )
       when checkSat(filter(F andBool V1 =/=Int V2)) ==K "unsat" 


  rule eqObs( <env>... X:Id |-> V1:K ...</env>
              <env>... X:Id |-> V2:K ...</env>
              <observers> ListItem(X) ...</observers>, F:K )
       =>
       false
       when checkSat(filter(F andBool V1 =/=Int V2)) ==K "sat"


/*@
  the equality of two (symbolic environments
*/

  syntax Bool ::= "eqEnv" "(" Map "," Map ")" [function]
  
  rule eqEnv(Env:Map, Env) => true

  rule eqEnv((X:K |-> V:K Env1:Map), (X |-> V Env2:Map)) => eqEnv(Env1, Env2)

  rule eqEnv((B:BExp |-> _ Env1:Map), Env2:Map) => eqEnv(Env1, Env2) 

  rule eqEnv(Env1:Map, (B:BExp |-> _ Env2:Map)) => eqEnv(Env1, Env2)

  rule eqEnv((A:AExp |-> _ Env1:Map), Env2:Map) => eqEnv(Env1, Env2) 

  rule eqEnv(Env1:Map, (A:AExp |-> _ Env2:Map)) => eqEnv(Env1, Env2)

  rule eqEnv(followup(S:Stmt, Env1:Map, F:Bool),
             followup(S:Stmt, Env2:Map, F':Bool))
       => 
       eqEnv(Env1, Env2)
       andBool checkSat(filter((F andBool notBool F') orBool 
                        (F' andBool notBool F)))
               ==K "unsat" 


/*@
  Try to compute the substitution between two programs:
*/

  syntax Map ::= "getSubst" "(" K "," K ")" [function]
              |  "noSubst"

  rule getSubst(K:K, K) => .Map

  rule getSubst(A1:K + A1':K, A2:K + A2':K)
       =>
       getSubst(A1, A2) getSubst(A1', A2')


  rule getSubst(A1:K * A1':K, A2:K * A2':K)
       =>
       getSubst(A1, A2) getSubst(A1', A2')


  rule getSubst(A1:K / A1':K, A2:K / A2':K)
       =>
       getSubst(A1, A2) getSubst(A1', A2')


  rule getSubst(A1:K <= A1':K, A2:K <= A2':K)
       =>
       getSubst(A1, A2) getSubst(A1', A2')


  rule getSubst(B1:K and B1':K, B2:K and B2':K)
       =>
       getSubst(B1, B2) getSubst(B1', B2')


  rule getSubst(B1:K and B1':K, B2:K and B2':K)
       =>
       getSubst(B1, B2) getSubst(B1', B2')


  rule getSubst(not B1:K, not B2:K) => getSubst(B1, B2)


  rule getSubst(S1:K ; S1':K, S2:K ; S2':K)
       =>
       getSubst(S1, S2) getSubst(S1', S2')


  rule getSubst(if B1:K then S1:K else S2:K, if B1':K then S1':K else S2':K)
       =>
       getSubst(B1, B1') getSubst(S1, S1') getSubst(S2, S2')


  rule getSubst(while B:K do S:K, while B':K do S':K)
       =>
       getSubst(B, B') getSubst(S, S')


  rule getSubst(for X:K from A1:K to A2:K do S:K,
                for X:K from A1':K to A2':K do S':K)
       =>
       getSubst(A1, A1')  getSubst(A2, A2') getSubst(S, S')


  rule getSubst(X:K := A1:K, X := A2:K) => getSubst(A1, A2)


  rule getSubst(K1:K ~> K2:K, K1':K ~> K2':K)
       =>
       getSubst(K1, K1') getSubst(K2, K2')
       when (K1 =/=K .K)
       andBool (K2 =/=K .K)
       andBool (K1' =/=K .K)
       andBool (K2' =/=K .K)

  rule getSubst(L1:Id : S1:K, L2:Id : S2:K) => getSubst(S1, S2)

  rule getSubst(I:K, A:K) => (I |-> A)
       when isSymbolicInt(I)

  rule getSubst(KL1:KLabel(_)~>_, KL2:KLabel(_)~>_) => noSubst
       when KL1 =/=KLabel KL2

  // to be completed

/*@
  Compute the substitution given by the maps stored in the environments
*/

  syntax Map ::= "getSubstMap" "(" Map "," Map ")" [function]

  rule getSubstMap(.Map, M:Map) => .Map

  rule getSubstMap((M1:Map B:BExp |-> V:K), M2:Map)
       =>
       getSubstMap(M1, M2) 
       when isSymbolicBool(B)

  rule getSubstMap((M1:Map A:AExp |-> V:K), M2:Map)
       =>
       getSubstMap(M1, M2) 
       when isSymbolicAExp(A)

  rule getSubstMap((M1:Map X:Id |-> I:K), (M2:Map X |-> A:K))
       =>
       I |-> A getSubstMap(M1, M2) 
       when isSymbolicInt(I)


  rule getSubstMap((M1:Map followup(S:Stmt, Env:Map, F:Bool)), M2:Map)
       =>
       getSubstMap(M1, M2)

  rule getSubstMap((#symbMap(IM:Id) M1:Map), M2:Map)
       =>
       getSubstMap(M1, M2)


/*@
  Check if a Map is a substitution (real map); only the false case is computed
*/

  syntax K ::= "isSubst" "(" Map ")" 

  rule isSubst(M:Map I:K |-> A:K I |-> B:K) => false
       when isSymbolicInt(I) andBool A =/=K B
       [anywhere]

    rule isSubst(_ noSubst ) => false

    rule ((X:K |-> A:K) (X:K |-> A:K)) => (X:K |-> A:K) [anywhere]

    rule noSubst noSubst => noSubst [anywhere]

/*@
   Apply a substitution to a symbolic boolean expression
*/

  syntax Bool ::= "applySubst" "(" Map "," K ")" [function]

  rule applySubst((M:Map I:K |-> A:K), F:Bool) => 
       applySubst(M:Map, (F [ A / I ]))
       when isSymbolicInt(I)
//       when M =/=Map .Map


  rule applySubst((I:K |-> A:K), F:Bool) => (F [ A / I ])
       when isSymbolicInt(I)

  rule applySubst(.Map, F:Bool) => F

  rule applySubst((noSubst _), F:Bool) => false // hmm, naybe it should be revised

/*@
   Extend the substitution to specific expressions:
*/

  rule (I:Id isNotModifiedBy S:Stmt) [E:K / V:K] => I isNotModifiedBy S  [anywhere]

/*@
  The predicate isMap4Subst:
*/

  syntax Bool ::= "isMap4Subst" "(" Map ")" [function]

  rule isMap4Subst(M:Map I:K |-> A:K) => isMap4Subst(M)
       when isSymbolicInt(I)
//       when M =/=Map .Map

  rule isMap4Subst(I:K |-> A:K) => true
       when isSymbolicInt(I)

  rule isMap4Subst(.Map) => true

  rule isMap4Subst(noSubst) => false


/*@
  The followings defines (special) cases when a current goal is a 
  consequence of the circular hypotheses.\\
  This relation must be more elaborated.
*/


  syntax K ::= "KItem" "(" Map ")"
  syntax K ::= "KItem" "(" Bag ")"
  syntax Bool ::= K "|-subst" K [function]

//rule KItem(<hypo> B1:Bag </hypo>) |-subst KItem(<goal> B2:Bag </goal>) => true [anywhere]


  rule KItem (H1:Bag H2:Bag) |-subst KItem(G:Bag)
       =>
       KItem (H1) |-subst KItem(G)
       orBool
       KItem (H2) |-subst KItem(G)
       when (KItem(H1) =/=K KItem(.Bag)) andBool (KItem(H2) =/=K KItem(.Bag))

syntax K ::= "break"

  rule KItem(.Bag) |-subst KItem(G:Bag) => false


  rule KItem(
     <hypo>      
       <condition>
         F:Bool
       </condition> 
       <patt1>        
         <k1>
          K1:K 
         </k1> 
         <env1>
          Rho1:Map
         </env1> 
       </patt1> 
       <patt2>        
         <k2> 
           K2:K
         </k2> 
         <env2>
          Rho2:Map
         </env2> 
       </patt2> 
     </hypo>) 

    |-subst

     KItem(<goal>      
       <condition>
         F':Bool
       </condition> 
       <config>        
         <k>
          K1':K 
         </k> 
         <env>
          Rho1':Map
         </env> 
       </config> 
       <config>        
         <k> 
          K2':K
         </k>
         <env>
          Rho2':Map
         </env>
       </config>
     </goal>)
     => 
     true
     when (((isMap4Subst(getSubst(K1, K1') getSubst(K2, K2')
                        getSubstMap(Rho1, Rho1') getSubstMap(Rho2, Rho2')
                       ) ==K true)
            andBool (isSubst(getSubst(K1, K1') getSubst(K2, K2')
                            getSubstMap(Rho1, Rho1') getSubstMap(Rho2, Rho2')
                           ) =/=K false)
            andBool (checkSat(filter(F' andBool 
                    notBool applySubst((getSubst(K1, K1') getSubst(K2, K2')
                                  getSubstMap(Rho1, Rho1') getSubstMap(Rho2, Rho2')), F)
                             )) ==K "unsat")

           ) orBool
           ((isMap4Subst(getSubst(K1, K2') getSubst(K2, K1')
                        getSubstMap(Rho1, Rho2') getSubstMap(Rho2, Rho1')
                       ) ==K true)
            andBool (isSubst(getSubst(K1, K2') getSubst(K2, K1')
                            getSubstMap(Rho1, Rho2') getSubstMap(Rho2, Rho1')
                           ) =/=K false)
            andBool (checkSat(filter(F' andBool 
                    notBool applySubst((getSubst(K1, K2') getSubst(K2, K1')
                                  getSubstMap(Rho1, Rho2') getSubstMap(Rho2, Rho1')), F)
                             )) ==K "unsat")

           )
          )

/*@
  The next rule gives semantics to the new construct \texttt{storeHyp}, which 
  consists of storing the hypothesis given by the arguments. Its semantics
  is similar to that of threads synchronization.\\
  TBD: replace the values of the program variables with fresh symbolic
  values and add to path condition the corresponding contraints.

  The case when both statements are labeled and
     the configurations are observational equal 
*/

  rule [store-hypo] :
       <goal>
         <config> 
           <k> storeHypo(L:Id, K1:K) => . ...</k>
           <env> Env1:Map </env>
         </config> 
         <config> 
           <k> storeHypo(L, K2:K) => . ...</k>
           <env> Env2:Map </env>
         </config>
         <condition> F:K </condition>
       </goal>
       <hypos>
         Hypos:Bag
         =>
         Hypos
         <hypo>
           <patt1> 
             <k1> K1 </k1>
             <env1> Env1 </env1>
           </patt1> 
           <patt2> 
             <k2> K2 </k2>
             <env2> Env2 </env2>
           </patt2>
           <condition> F </condition>
         </hypo>
       </hypos>
       <observers> Obs:List </observers>
       when (eqObs(<env> Env1 </env> 
                   <env> Env2 </env> 
                   <observers> Obs </observers>, F) ==K true)
            andBool
            ((KItem(Hypos)
            |-subst
            KItem(<goal>
               <config> 
                 <k> K1 </k>
                 <env> Env1 </env>
               </config> 
               <config> 
                 <k> K2 </k>
                 <env> Env2 </env>
               </config>
               <condition> F </condition>
             </goal>))
             =/=K true)
       [transition]


  /*@
     The case when both statements are labeled and
     the configurations are NOT observational equal 
  */ 
  rule [store-hypo]:
       <goal>
         <config> 
           <k> storeHypo(L:Id, K1:K) => . ...</k>
           <env> Env1:Map </env>
         </config> 
         <config> 
           <k> storeHypo(L, K2:K) => . ...</k>
           <env> Env2:Map </env>
         </config>
         <condition> F:K </condition>
       </goal>
       <hypos>
         Hypos:Bag
       </hypos>
       <observers> Obs:List </observers>
       when
       eqObs(<env> Env1 </env> 
             <env> Env2 </env> 
             <observers> Obs </observers>, F) =/=K true
       [transition]


/*@
  The next rule is intended to implement the entailment between the collected
  hypotheses and goals. Obviously, this is a partial implementation. Again,
  the formulas are ignored for now, because they are considered equal.
*/

  rule [circularity] :
       (<goal>
         <config> 
           <k> storeHypo(L:Id, K1:K) ...</k>
           <env> Env1:Map </env>
         </config> 
         <config> 
           <k> storeHypo(L, K2:K) ...</k>
           <env> Env2:Map </env>
         </config>
         <condition> F:K </condition>
        </goal>
        =>
        success
       )
       <hypos> Hypos:Bag </hypos>
       when
       (KItem(Hypos)
        |-subst 
        KItem(<goal>
         <config> 
           <k> K1 </k>
           <env> Env1 </env>
         </config> 
         <config> 
           <k> K2 </k>
           <env> Env2 </env>
         </config>
         <condition> F </condition>
        </goal>)
      ) ==K true
     [transition]

/*@
  The following rule creates the initial configuration from the equivalence
  specification given as input.
*/

  rule [initial] :
       <config>
         <k> 
           <k> P1:Stmt </k>
           <env> Inits1:InitVals </env>
           ~
           <k> P2:Stmt </k>
           <env> Inits2:InitVals </env>
           if F:BExp
           using observers: Obs:Ids; 
           =>
           setInitValObs(Obs) ~> setInitVal(Inits1) ~> P1
         </k>
       ...</config>
       <condition> _ => injectForm(F) </condition>
      (. =>
       <config>
         <k> 
           setInitValObs(Obs) ~> setInitVal(Inits2) ~> P2
         </k>
         <env> . </env>
       </config>)
       <observers> . => Ids2List(Obs) </observers>

/*@
  The auxiliary construct \texttt{initVal()} is used for initializing the 
  observer variables with the same values in the two initial program
  configurations. 
*/


  syntax K ::= "setInitVal" "(" InitVals ")"

  rule setInitVal(.InitVals) => .
       [structural]

  rule <k> setInitVal((X:Id -> V:Int, XVs:InitVals) => XVs) ...</k>
       <env>... . => X |-> V ...</env>
       [structural]

  rule <k> setInitVal((SymMap(M:Id), XVs:InitVals) => XVs) ...</k>
       <env>... . => #symbMap(M) ...</env>
       [structural]

  syntax K ::= "setInitValObs" "(" Ids ")"

  rule <k> setInitValObs(.Ids) => . ...</k>
       <k> setInitValObs(.Ids) => . ...</k>
       [structural]

  rule <k> setInitValObs(allObs) => . ...</k>
       <k> setInitValObs(allObs) => . ...</k>
       [structural]


  rule <config>
         <k> setInitValObs((X:Id, Xs:Ids) => Xs) ...</k>
         <env>... . => X |-> IS1 ...</env>
       </config> 
       <config> 
         <k> setInitValObs((X:Id, Xs:Ids) => Xs) ...</k>
         <env>... . => X |-> IS2 ...</env>
       </config> 
       <condition> B:K => B andBool (IS1 ==Int IS2) </condition>
//       <nextSymVar> I:Int => I +Int 2 </nextSymVar>
       when fresh(IS1:Int) andBool fresh(IS2:Int)
       [structural]


/*@ 
  The next function translates the initial condition into internal
  form.\\
  TBD: refactor it!!!!
*/


  syntax Bool ::= "injectForm" "(" BExp ")" [function]

  rule injectForm(true) => true

  rule injectForm(A1:AExp == A2:AExp)
       =>
       injectAExp(A1)  ==Int injectAExp(A2)


  rule injectForm(B1:BExp and B2:BExp)
       =>
       injectForm(B1) andBool injectForm(B2)


  rule injectForm(not B:BExp)
       =>
       notBool injectForm(B)


  syntax Int ::= "injectAExp" "(" AExp ")" [function]
  rule injectAExp(I:Int) => I
  rule injectAExp(A1:AExp + A2:AExp)
       =>
       injectAExp(A1)  +Int injectAExp(A2)


  rule injectAExp(A1:AExp * A2:AExp)
       =>
       injectAExp(A1)  *Int injectAExp(A2)


  rule injectAExp(A1:AExp / A2:AExp)
       =>
       injectAExp(A1)  /Int injectAExp(A2)


  rule injectForm(X:Id isNotModifiedBy S:Stmt ) 
       =>
       X isNotModifiedBy S


  rule injectForm(occurs(X:Id, S:Stmt)) 
       =>
       occurs(X, S) 


/*@
  The following is a helper function that transform a list of
  identifiers into a builtin list; it is used for storing the observer
  variables into the cell \texttt{observers}.
*/ 
  syntax List ::= "Ids2List" "(" Ids ")" [function]
  rule Ids2List(.Ids) => .List
  rule Ids2List(X:Id, Xs:Ids) => ListItem(X) Ids2List(Xs)


//  syntax List ::= "BExps2List" "(" BExps ")" [function]
//  rule BExps2List(.BExps) => .List [anywhere]
//  rule BExps2List(X:BExp, Xs:BExps) => ListItem(X) BExps2List(Xs)
//       [anywhere]

//@ rules that translate the locally defined predicates to SMTLIB

//  rule Consts2SMTLib( X:Id isNotModifiedBy S:Stmt ) => .Set [anywhere]
//  rule Vars2SMTLib( X:Id isNotModifiedBy S:Stmt ) => .Set [anywhere]
//  rule K2SMTLib( X:Id isNotModifiedBy S:Stmt ) => "true" [anywhere]

  syntax Bool ::= "filter" "(" Bool ")" [function]
               |  "replaceIsNotModifiedBy" "(" Bool "," Bool ")" [function]

  rule replaceIsNotModifiedBy(B:Bool, X:Id isNotModifiedBy S:Stmt) => B

//  rule replaceIsNotModifiedBy(B:Bool, KL:KLabel(L:List{K})) => KL(L)
//       when isSymbolicBool(KL(L)) andBool 
//            (KL =/=KLabel '_isNotModifiedBy_)

// trick:
  rule replaceIsNotModifiedBy(B:Bool, I1:Int <=Int I2:Int) => I1 <=Int I2 

  rule replaceIsNotModifiedBy(B:Bool, I1:Int ==Int I2:Int) => I1 ==Int I2

  rule replaceIsNotModifiedBy(B:Bool, notBool B1:Bool)
       =>
       notBool replaceIsNotModifiedBy(B, B1)

  rule replaceIsNotModifiedBy(B:Bool, B1:Bool andBool B2:Bool)
       =>
       replaceIsNotModifiedBy(B, B1) andBool replaceIsNotModifiedBy(B, B2)

  rule replaceIsNotModifiedBy(B:Bool, B1:Bool orBool B2:Bool)
       =>
       replaceIsNotModifiedBy(B, B1) orBool replaceIsNotModifiedBy(B, B2)

  rule replaceIsNotModifiedBy(B:Bool, B1:Bool impliesBool B2:Bool)
       =>
       replaceIsNotModifiedBy(B, B1) impliesBool replaceIsNotModifiedBy(B, B2)


  rule filter(B:Bool) => replaceIsNotModifiedBy(true, B) orBool
                        replaceIsNotModifiedBy(false, B)

/*@
  The following defines the substitution of the symbolic values with
  symbolic expressions.
  This should be defined in a more generic way using ASTs.
*/

  syntax K ::= K "[" K "/" K "]"

  rule (F1:K andBool F2:K) [ V:K / X:K ]
        =>
        (F1 [ V:K / X:K ]) andBool (F2[ V:K / X:K ])
        [anywhere]

  rule (notBool F:K) [ V:K / X:K ]
        =>
        notBool (F[ V:K / X:K ])
        [anywhere]


  rule (I1:Int <=Int I2:Int) [ E1:K / E2:K ]
       =>
       (I1 [ E1 / E2 ]) <=Int (I2 [ E1 / E2 ])
       [anywhere]

  rule (I1:Int ==Int I2:Int) [ E1:K / E2:K ]
       =>
       (I1 [ E1 / E2 ]) ==Int (I2 [ E1 / E2 ])
       [anywhere]

  rule (I1:Int +Int I2:Int) [ E1:K / E2:K ]
       =>
       (I1 [ E1 / E2 ]) +Int (I2 [ E1 / E2 ])
       [anywhere]

  rule (I1:Int *Int I2:Int) [ E1:K / E2:K ]
       =>
       (I1 [ E1 / E2 ]) *Int (I2 [ E1 / E2 ])
       [anywhere]

  rule I:Int [ E1:K / E2:K ] => E1 
       when I ==K E2
       [anywhere]
 
  rule I:Int [ E1:K / E2:K ] => I
       when I =/=K E2
       [anywhere]

  rule (I1:Int ==Int I2:Int) andBool F:K impliesBool B:K
       =>
       (F impliesBool (B [ I2 / I1 ]))
       [anywhere]

  rule (I1:Int ==Int I2:Int) impliesBool B:K
       =>
       B [ I2 / I1 ]
       [anywhere]


  rule B:Bool impliesBool true => true  [anywhere]

  rule (B:Bool andBool B':Bool) impliesBool B => true  [anywhere]
  rule (B':Bool andBool B:Bool) impliesBool B => true  [anywhere]

  rule B:Bool andBool true => B  [anywhere]

  rule true andBool B:Bool => B  [anywhere]

  rule B:Bool andBool B => B  [anywhere]

  rule (B1:Bool andBool B:Bool) andBool B => B1 andBool B  [anywhere]

  rule B:Bool orBool true => true  [anywhere]

  rule true orBool B:Bool => true  [anywhere]

  rule B:Bool impliesBool B => true [anywhere]

endmodule
