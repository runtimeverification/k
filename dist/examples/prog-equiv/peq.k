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

  syntax Bool ::= K "isNotModifiedBy" K [function]

  rule X:Int isNotModifiedBy _:K => true when isSymbolicInt(X) [anywhere]
  rule X:Bool isNotModifiedBy _:K => true when isSymbolicBool(X)  [anywhere]

  syntax Map ::= "followup" "(" K "," Map "," Bool ")"
  rule isSymbolicMap(followup(_:K, _:Map, _:Bool)) => true [anywhere]

  rule followup(S:K, (X:K |-> V:K M:Map), F:Bool) 
       =>
       X |-> V followup(S, M, F)
       when isSymbolicInt(X) // to be revised
       [anywhere]

  rule followup(S:K, (X:K |-> V:K M:Map), F:Bool) 
       =>
       X |-> V followup(S, M, F)
       when isSymbolicBool(X) // to be revised
       [anywhere]


  rule followup(S:K, (X:K |-> V:K M:Map), F:Bool) 
       =>
       X |-> V followup(S, M, F)
       when (F impliesBool (X isNotModifiedBy S)) // it does not work; to be revised
       [anywhere]

// temporary solution until the correct sorting of #symMap() is solved 

  syntax Map ::= "#symbMap" "(" Id ")"
  rule isSymbolicMap(#symbMap(_:Id)) => true [anywhere]

  //@ Extend keys()
  rule keys ((followup(_:K, _:Map, _:Bool) => .) _) [structural]
  rule keys ((#symbMap(_) => .) _) [structural]

  //@ Lookup
  syntax K ::= "lookup" "(" K "," Map ")" [function]
  rule [lookup] :  lookup(X:K, (_ X |-> V:K _)) => V

  rule [lookup] :
       lookup(X:K, followup(SS:K, Rho:Map, F:Bool)) 
        => 
        lookup(X, Rho)
        when //isSymbolicStmt(SS) andBool 
        F impliesBool (X isNotModifiedBy SS) // to be revised

  rule [lookup] :
       lookup(X:K, followup(_:K, Rho:Map, _:Bool) Rho':Map) 
       => 
       lookup(X, Rho)
       when //isSymbolicStmt(SS) andBool 
     //  F impliesBool (X isNotModifiedBy SS)  andBool 
       notBool(X in keys(Rho')) // to be revised

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


  syntax Stmt ::= "skip" | Elt | Elt "::" Stmt | Id ":-" Stmt
  				| Id ":=" AExp   [strict(2)]
  				| "if" BExp "then" Stmt "else" Stmt [strict(1)]
  				| "while" BExp "do" Stmt
                                | "for" Id "from" AExp "to" AExp "do" Stmt
                                  [strict(2, 3)] 
                                | Id ":" Stmt
  				> Stmt ";" Stmt   [left]
  				| "(" Stmt ")"    [bracket]

  syntax Elt ::= Id | Int   // extension for streams

//  syntax Stmt ::= Elt | Elt "::" Stmt | Id ":-" Stmt

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

  //@ the predicate for occurrence of a variable in a statement
  syntax Bool ::= "occurs" "(" Id "," Stmt ")"

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
		  <output stream="stdout"> ListItem("Proving ...\n") </output>
                  <hypos>
                    <hypo multiplicity="*">
                      <patt1>
                        <hk1 color="green"> .K  </hk1>
                        <henv1 color="red"> .Map </henv1>
                      </patt1>
                      <patt2>
                        <hk2 color="green"> .K  </hk2>
                        <henv2 color="red"> .Map </henv2>
                      </patt2>
                      <hcondition> true </hcondition>
                    </hypo>
                  </hypos>
                  <observers> .List </observers>
                </T>

/*@
  The values are defined as for the original IMP, but note that now Int includes
  the symbolic integer expressions. Remember that the predicate \texttt{isBool} 
  is not extended to symbolic boolean expressions. So, the only boolean values 
  remain \texttt{true} and \texttt{false}.
*/

  syntax KResult ::= Val
  syntax Val ::= Int | #Bool // | "val" "(" Bool ")"

/*@
  We use a new syntactic construct that help us to store hypotheses. The basic
  idea is to add the hypotheses in a controlled way. For instance, we may add
  hypothesis only when on the top in the two k cells we have  statement with
  the same label (the label is a kind of "rendevous" synchronisarion). 
*/

  syntax K ::= "storeHypo" "(" K ")"   // for storing hypotheses
            |  "lbldStmt" "(" Id "," K ")"    // event signalling a labelled
                                              // statement

            |  "checkHypo" "(" K "," Map "," K "," Map "," HyposCellFragment ")"
               // for checking hypotheses one by one 

            |  "checkCond" "(" K "," K ")"  // check the conditions of the
                                     // current formula and checked hypothesis

  syntax K ::= "break"  // to temporarily stop one of the two programs


  rule notBool occurs(X:K, S:K) => (X  isNotModifiedBy S) [anywhere]  //trick



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
  rule [and-false]: false and _:BExp => false

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

  rule [sequential] : S1:Stmt;S2:Stmt => S1 ~> S2 [structural]

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
//       [transition] 


/*@ \subsection{Labelled statements}
  We first extend the contextual declarations (derived from the strictness
  attribute) to the labelled transitions.
*/


/*@
  The labelled recursive statements have a special semantics because
  the label must be propagated. Therefore we need a boolean function
  that discriminate between recursive and non-recursive statements.
*/

  syntax Boolean ::= "isRecursive" "(" Stmt ")" [function]
  rule isRecursive(while _:BExp do _:Stmt) => true
  rule isRecursive(for I:Id from A1:AExp to A2:AExp do S:Stmt) => true


/*@
  For the non-recursive statements, the labels are translated into 
  synchronyzing construct. Naturally, for these cases only the label
  is required for the synchronization. We prefer to save the whole
  content of the cell \texttt{k} as argument of the synchronyzing
*/

  rule [labelled-non-rec-stmt] :
       <k>
          ( L:Id : S:Stmt
            =>
            lbldStmt(L, S ~> K) ~> S
          ) ~> K:K 
       </k>
       when isRecursive (S) =/=K true
//       [transition]

/*@
  The two labeled recursive statements have a special semantics due to the
  label  propagation.
*/

  rule [while-labelled] :
       <k>
          L:Id : while B:BExp do S:Stmt ~> K:K
          => 
          lbldStmt(L, while B do S ~> K) ~>
          if B then S ; L : while B do S else skip
          ~> K
       </k> 
//       [transition]

  rule [for-labelled]:  
        <k> 
          L:Id : for I:Id from A1:AExp to A2:AExp do S:Stmt ~> K:K
           => 
          lbldStmt(L, for I from A1 to A2 do S ~> K) ~>
          I := A1;
          if (I <= A2) then (S; L : for I from (A1 + 1) to A2  do S)
                       else skip
          ~> K
        </k> 
//       [transition]

/*@
  Semantics of the symbolic statements:
*/


  rule [symbolic-stmt] : 
<config>...
       <k> #symStmt(SS:K) => .  ...</k>
       <env> M:Map => followup(#symStmt(SS), M, F) </env>
...</config>
       <condition> F:Bool </condition>
//       when isSymbolicStmt(SS)
//       [transition] 


  rule [symbolic-aexp] :
       <k> #symAExp(XS:K) => lookup(#symAExp(XS), Rho) ...</k>
       <env> Rho:Map </env>
       when #symAExp(XS) in keys(Rho)
//       [transition]

  rule [symbolic-aexp] : 
       <config>... 
         <k> #symAExp(XS:K) =>  VS ...</k>
         <env> Rho:Map => update(Rho, #symAExp(XS), VS) </env>
       ...</config>
       <config>...
         <env> Rho':Map => update(Rho', #symAExp(XS), VS) </env>
       ...</config>
       when (notBool #symAExp(XS) in keys(Rho)) andBool fresh(VS:Int)
//       [transition] 

/*@
  The memory lookup rule is changed because now the memory can be a 
  symbolic one obtained after a the execution of a symbolic statement.
*/


  rule [lookup] : 
       <k> X:Id =>  lookup(X, Rho) ...</k>
       <env> Rho:Map </env> 
//       [transition] 

/*@
  The semantics of the assignment is modified because of the symbolic  
  statements.
*/

  rule [assignment]:
       <k> X:Id := I:Int => . ...</k>
       <env> Rho:Map => update(Rho, X, I) </env>
//       [transition]


/*@
  additional rules that conservatively extend the definition
*/

  rule [symb-boolean] :
<config>...
       <k>
          B:Bool
          =>
          checkSat(filter(F andBool B)) ~> 
          checkSat(filter(F andBool notBool B)) ~> 
          B
       ...</k>
       <env> Rho:Map </env>
...</config>
       <condition> F:Bool </condition>
       when isSymbolicBool(B)  andBool notBool(B in keys(Rho))
//       [transition]

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
//       [transition]

  rule [sym-bool-red-to-false] :
       "unsat" ~> "sat" ~> B:K => false // F impliesBool notBool B
       when isSymbolicBool(B) 
//       [transition]

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

  rule (<goals> .Bag </goals> => .)
       <output> _ => ListItem("true") </output>


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
       .)
       <observers> Obs:List </observers>
       when eqObs(<env> Env </env>, 
                  <env> Env' </env>,
                  <observers> Obs </observers>, F)
            ==K true
//       [transition]


/*@
  The observational equivalence relation is defined by checking the equality of
  the observer variables in the two configurations (see how \texttt{eqObs} is 
  called.
*/

  syntax Bool ::= "eqObs" "(" EnvCellSort "," EnvCellSort "," ObserversCellSort "," K ")" [function]

  rule eqObs(<env> _ </env>,
             <env> _ </env>,
             <observers> .List </observers>, F:K)
       =>
       true


  rule eqObs(<env> Env1:Map </env>,
             <env> Env2:Map </env>,
             <observers> ListItem(allObs) </observers>, F:K)
       =>
       eqEnv(Env1, Env2)


  rule eqObs( <env>... X:Id |-> V1:Int ...</env>,
              <env>... X    |-> V2:Int ...</env>,
              <observers> ListItem(X) => . ...</observers>, F:K )
       when checkSat(filter(F andBool notBool(V1 ==Int V2))) ==K "unsat" 
// when V1 ==K V2

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

  syntax Exp ::= "getSubst" "(" K "," K "," Map ")" [function]
            |  K "replBy" K [strict(2)]  // a substitution pair
            |  Exp ";;" Exp [left, strict]      // concatenation of substitutions
            |  "emptySubst"
            | Val

  rule getSubst(K:K, K, M:Map) => emptySubst

  rule getSubst(A1:K + A1':K, A2:K + A2':K, M:Map)
       =>
       getSubst(A1, A2, M) ;; getSubst(A1', A2', M)


  rule getSubst(A1:K * A1':K, A2:K * A2':K, M:Map)
       =>
       getSubst(A1, A2, M) ;; getSubst(A1', A2', M)


  rule getSubst(A1:K / A1':K, A2:K / A2':K, M:Map)
       =>
       getSubst(A1, A2, M) ;;  getSubst(A1', A2', M)


  rule getSubst(A1:K <= A1':K, A2:K <= A2':K, M:Map)
       =>
       getSubst(A1, A2, M) ;; getSubst(A1', A2', M)


  rule getSubst(B1:K and B1':K, B2:K and B2':K, M:Map)
       =>
       getSubst(B1, B2, M) ;; getSubst(B1', B2', M)


  rule getSubst(B1:K and B1':K, B2:K and B2':K, M:Map)
       =>
       getSubst(B1, B2, M) ;; getSubst(B1', B2', M)


  rule getSubst(not B1:K, not B2:K, M:Map) => getSubst(B1, B2, M)


  rule getSubst(S1:K ; S1':K, S2:K ; S2':K, M:Map)
       =>
       getSubst(S1, S2, M) ;; getSubst(S1', S2', M)


  rule getSubst(if B1:K then S1:K else S2:K, if B1':K then S1':K else S2':K, M:Map)
       =>
       getSubst(B1, B1', M) ;; getSubst(S1, S1', M) ;; getSubst(S2, S2', M)


  rule getSubst(while B:K do S:K, while B':K do S':K, M:Map)
       =>
       getSubst(B, B', M) ;; getSubst(S, S', M)


  rule getSubst(for X:K from A1:K to A2:K do S:K,
                for X:K from A1':K to A2':K do S':K, M:Map)
       =>
       getSubst(A1, A1', M) ;; getSubst(A2, A2', M) ;; getSubst(S, S', M)


  rule getSubst(X:K := A1:K, X := A2:K, M:Map) => getSubst(A1, A2, M:Map)


  rule getSubst(K1:K ;; K2:K, K1':K ;; K2':K, M:Map)
       =>
       getSubst(K1, K1', M) ;; getSubst(K2, K2', M)
       when (K1 =/=K .K)
       andBool (K2 =/=K .K)
       andBool (K1' =/=K .K)
       andBool (K2' =/=K .K)

  rule getSubst(L1:Id : S1:K, L2:Id : S2:K, M:Map) => getSubst(S1, S2, M)


  rule getSubst(X:K, A:AExp, (M:Map X |-> I:Int)) => (I replBy A)
       when (isId(X) ==K true) orBool (isSymbolicAExp(X) ==K true) 

  rule getSubst(X:Id, B:BExp, (M:Map X |-> I:Int)) => (I replBy B)


  // to be completed

/*@
  Compute the substitution given by the maps stored in the environments
*/

  syntax Map ::= "getSubstMap" "(" Map "," Map ")" [function]

  rule getSubstMap(.Map, M:Map) => .Map

  rule getSubstMap((M1:Map E:K |-> V:K), M2:Map)
       =>
       getSubstMap(M1, M2) 
       when (isSymbolicBool(E) ==K true) orBool (isSymbolicAExp(E) ==K true)


  rule getSubstMap((M1:Map X:Id |-> I:K), (M2:Map X |-> A:K))
       =>
       I |-> A getSubstMap(M1, M2) 
       when isSymbolicInt(I) ==K true

  rule getSubstMap((M1:Map X:Id |-> I:K), (M2:Map X |-> A:K))
       =>
       getSubstMap(M1, M2) 
       when isSymbolicInt(I) =/=K true

  rule getSubstMap((M1:Map followup(S:Stmt, Env:Map, F:Bool)), M2:Map)
       =>
       getSubstMap(M1, M2)

  rule getSubstMap((#symbMap(IM:Id) M1:Map), M2:Map)
       =>
       getSubstMap(M1, M2)


/*@
  Check if a Map is a substitution (real map); only the false case is computed
*/

  syntax K ::= "isSubst" "(" K ")"  [function]

  rule isSubst(emptySubst) => true

  rule isSubst(M:K ;; (I:K replBy A:K)) => isSubst(M)


 //@ Two auxiliary rules

  rule ((X:K |-> A:K) (X:K |-> A:K)) => (X:K |-> A:K) [anywhere]

  rule E:Exp ;; emptySubst => E

  rule emptySubst ;; E:Exp => E



/*@
  The followings defines (special) cases when a current goal is a 
  consequence of the circular hypotheses.\\
  This relation must be more elaborated.
*/


/*@
  When two statemets with the same label are synchronized, there are two ways
  to continue:
  1) apply circularity deduction rule if there is an hypothesis that matches the current
     formula;
  2) store the current formula as a circular hypothesis when such an hypothesis does not
     exist.
  We use the auxiliary semantic statement checkHypo for deciding between the two cases.
  Note: the semantics of lbldStmt is similar to that of threads synchronization.
*/

  rule [lbld-stmt-sync] : 
       <goal>
         <config> 
           <k> lbldStmt(L:Id, K1:K) => checkHypo(K1, Env1, K2, Env2, Hypos) ...</k>
           <env> Env1:Map </env>
         </config> 
         <config> 
           <k> lbldStmt(L, K2:K) => break ...</k>
           <env> Env2:Map </env>
         </config>
         <condition> F:Bool </condition>
       </goal>
       <hypos>
         Hypos:Bag
       </hypos>
//      [transition]

  /*@ The case when the set of hypotheses is empty and 
       the configurations are observational equal.
       The formula is stored as circularity hypo
  */

  rule [check-hypo-no-hyp-obseq] : 
       <goal>
         <config> 
           <k> checkHypo(K1:K, Env1:Map, K2:K, Env2:Map, .Bag) => storeHypo(K1) ...</k>
           <env> _ => Env1 </env>
         </config> 
         <config> 
           <k> break => storeHypo(K2) ...</k>
         ...</config>
         <condition> F:Bool </condition>
       ...</goal> 
       <observers> Obs:List </observers> 
       when (eqObs(<env> Env1 </env>, 
                   <env> Env2 </env>,
                   <observers> Obs </observers>, F) ==K true)
//       [transition]


/*@
  Check hypotheses.
  This is the most tricky step since we have to find a substitution from an
  hypothesis configuration and the current configuration and check that the
  current path (formal) condition implies the formula obtained by applying
  the substitution restrictied to the environment component to the hypothesis
  path formula, as well the formula representing the substitution restricted
  to program (k cell) component.
  Recall that the substitution given by the environment (env cell) is obtained
  with getMapSubst(), and that given by programs is obtained with getSubst().
  Sibce the configurations in the current formula are unordered, we have 
  to check two cases.
*/

  rule [check-hypo] :
       <goal>
         <config> 
           <k> checkHypo(K1:K, Env1:Map, K2:K, Env2:Map, 
     	       		               	     <hypo>      
       					       <hcondition>
					         F':Bool
       					       </hcondition> 
       					       <patt1>        
         				         <hk1>
          					   K1':K 
         					 </hk1> 
         					 <henv1>
          					   Env1':Map
          					 </henv1> 
       					       </patt1> 
       					       <patt2>        
         				         <hk2> 
           					   K2':K
						 </hk2> 
         					 <henv2>
         					   Env2':Map
         					 </henv2> 
       					       </patt2> 
     					     </hypo>
                                             Hypos':Bag
                      )
            =>
           checkCond(F, F')
           ...</k>
         ...</config> 
         <config> 
           <k> break ...</k>
         ...</config>
         <condition> F:K </condition>
       </goal>
       when (isSubst(getSubst(K1', K1, Env1')) ==K true)
            orBool (isSubst(getSubst(K2', K2, Env2')) ==K true)
 //      [transition]

  rule [check-hypo] :
       <goal>
         <config> 
           <k> checkHypo(K1:K, Env1:Map, K2:K, Env2:Map, 
     	       		               	     <hypo>      
       					       <hcondition>
					         F':Bool
       					       </hcondition> 
       					       <patt1>        
         				         <hk1>
          					   K1':K 
         					 </hk1> 
         					 <henv1>
          					   Env1':Map
          					 </henv1> 
       					       </patt1> 
       					       <patt2>        
         				         <hk2> 
           					   K2':K
						 </hk2> 
         					 <henv2>
         					   Env2':Map
         					 </henv2> 
       					       </patt2> 
     					     </hypo>
                                             Hypos':Bag
                      )
            =>
           checkCond(F, F')
           ...</k>
         ...</config> 
         <config> 
           <k> break ...</k>
         ...</config>
         <condition> F:K </condition>
       </goal>
       when (isSubst(getSubst(K1', K2, Env1')) ==K true)
            orBool (isSubst(getSubst(K2', K1, Env2')) ==K true)
//       [transition]


  /*@ The case when the circularity rule can be applied;
      both the substitution and the conditions are successfully checked
     TBD: The condition does not verify now, to be revised
  */
  rule [circularity] :
       (<goal>
         <config> 
           <k> checkCond(F:K, SF':K) ...</k>
         ...</config> 
         <config> 
           <k> break ...</k>
         ...</config>
         <condition> F:K </condition>
       </goal>
       =>
       .)
       when checkSat(filter(F andBool notBool(SF'))) ==K "unsat"

/*@
  The case when an hypothesis does not match the current formula.
*/ 

  rule [check-hyp-fail] :
       <goal>
         <config> 
           <k> checkHypo(K1:K, Env1:Map, K2:K, Env2:Map, 
     	       		               	     (<hypo>      
       					       <hcondition>
					       F':Bool
       					       </hcondition> 
       					       <patt1>        
         				         <hk1>
          					   K1':K 
         					 </hk1> 
         					 <henv1>
          					   Env1':Map
          					 </henv1> 
       					       </patt1> 
       					       <patt2>        
         				         <hk2> 
           					   K2':K
						 </hk2> 
         					 <henv2>
         					   Env2':Map
         					 </henv2> 
       					       </patt2> 
     					     </hypo>
                        		     =>
					     .
                                            )
                                           Hypos':Bag
                        )
           ...</k>
           <env> _ => Env1 </env>
         ...</config> 
         <config> 
           <k> break ...</k>
         ...</config>
         <condition> F:K </condition>
       ...</goal>
       <observers> Obs:List </observers>
       when ((isSubst(getSubst(K1', K1, Env1')) =/=K true)
             orBool (isSubst(getSubst(K2', K2, Env2')) =/=K true)
            ) andBool
            ((isSubst(getSubst(K1', K2, Env1')) =/=K true)
             orBool (isSubst(getSubst(K2', K1, Env2')) =/=K true)
            )
//       [transition]

  //@ The rules preparing the storing of an hypothesis: 
  rule [store-hypo] :
       <config> 
//         <k> storeHypo(K1:K) => getFresh(Env1) ~> restore(K1, Env1) ...</k>
         <k> storeHypo(K1:K) => restore(K1, Env1) ...</k>
         <env> Env1:Map </env>
       </config> 
//       [transition]


  //@ Generates fresh symbolic values for the stored hypothesis
  syntax K ::= "getFresh" "(" Map ")"

  rule [getFresh] :
       <config>
         <k> getFresh(((X:Id |-> _:Int) => .) _ ) ...</k>
         <env>... X |-> (V:Int => VS) ...</env>
       </config>
       <condition> F:Bool => (F andBool (VS ==Int V)) </condition>
       when fresh(VS:Int)

  rule [getFresh] :
       getFresh((X:K |-> V:K => .) _)
       when (isId(X) =/=K true) orBool (isInt(V) =/=K true)

  rule [getFresh] :
       getFresh((#symbMap(_) => .) _)

  rule [getFresh] :
       getFresh((followup(_,_,_) => .) _)

  rule getFresh(.Map) => .K

  syntax K ::= "restore" "(" K "," Map ")"

  rule [restore] :
       <goal>
         <config> 
           <k> restore(K1:K, Env1':Map) => . ...</k>
           <env> Env1:Map => Env1' </env>
         </config> 
         <config> 
           <k> restore(K2:K, Env2':Map) => . ...</k>
           <env> Env2:Map => Env2' </env>
         </config>
         <condition> F:Bool </condition>
       </goal>
       <hypos>
         Hypos:Bag
         =>
         Hypos
         <hypo>
           <patt1> 
             <hk1> K1 </hk1>
             <henv1> Env1 </henv1>
           </patt1> 
           <patt2> 
             <hk2> K2 </hk2>
             <henv2> Env2 </henv2>
           </patt2>
           <hcondition> F </hcondition>
         </hypo>
       </hypos>
//      [transition]


  /*@
     The case when both statements are labeled and
     the configurations are NOT observational equal 
  */ 
  rule [store-hypo-fail]:
       <goal>
         <config> 
           <k> lbldStmt(L1:Id, K1:K) => . ...</k>
           <env> Env1:Map </env>
         </config> 
         <config> 
           <k> lbldStmt(L2:Id, K2:K) => . ...</k>
           <env> Env2:Map </env>
         </config>
         <condition> F:K </condition>
       </goal>
       <observers> Obs:List </observers>
       when
       (L1 =/=K L2) orBool
       (eqObs(<env> Env1 </env>, 
             <env> Env2 </env>, 
             <observers> Obs </observers>, F) =/=K true)
//       [transition]

/*
  rule [store-hypo-fail]:
       <goal>
         <config> 
           <k> lbldStmt(L1:Id, K1:K) => . ...</k>
           <env> Env1:Map </env>
         </config> 
         <config> 
           <k> lbldStmt(L2:Id, K2:K) ...</k>
           <env> Env2:Map </env>
         </config>
         <condition> F:K </condition>
       </goal>
       <observers> Obs:List </observers>
       when
       (L1 =/=K L2) orBool
       (eqObs(<env> Env1 </env> 
             <env> Env2 </env> 
             <observers> Obs </observers>, F) =/=K true)
       [transition]

  rule [store-hypo-fail]:
       <goal>
         <config> 
           <k> lbldStmt(L1:Id, K1:K) ...</k>
           <env> Env1:Map </env>
         </config> 
         <config> 
           <k> lbldStmt(L2:Id, K2:K) => . ...</k>
           <env> Env2:Map </env>
         </config>
         <condition> F:K </condition>
       </goal>
       <observers> Obs:List </observers>
       when
       (L1 =/=K L2) orBool
       (eqObs(<env> Env1 </env> 
             <env> Env2 </env> 
             <observers> Obs </observers>, F) =/=K true)
       [transition]
*/

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
           setInitVal(Inits1) ~> setInitValObs(Obs) ~> P1
         </k>
       ...</config>
       <condition> _ => injectForm(F) </condition>
      (. =>
       <config>
         <k> 
           setInitVal(Inits2) ~> setInitValObs(Obs) ~> P2
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

  /*@ The values for observers must be different, in order to correctly 
      define substitution.
  */

  rule <config>
         <k> setInitValObs((X:Id, Xs:Ids) => Xs) ...</k>
         <env> Env:Map (. => X |-> IS1) </env>
       </config> 
       <config> 
         <k> setInitValObs((X:Id, Xs:Ids) => Xs) ...</k>
         <env>... . => X |-> IS2 ...</env>
       </config> 
       <condition> B:K => B andBool (IS1 ==Int IS2) </condition>
       when (fresh(IS1:Int) andBool fresh(IS2:Int)) andBool notBool(X in keys(Env))
       [structural]

  rule <config>
         <k> setInitValObs((X:Id, Xs:Ids) => Xs) ...</k>
         <env> Env:Map </env>
       </config> 
       when (X in keys(Env))
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


//@ rules that translate the locally defined predicates to SMTLIB


/*@
  Helper functions that are used for cleaning a formula before sending it 
  to the SMT solver.
*/

  syntax Bool ::= "filter" "(" Bool ")" [function]
               |  "replaceIsNotModifiedBy" "(" Bool "," Bool ")" [function]

  rule replaceIsNotModifiedBy(B:Bool, X:Id isNotModifiedBy S:Stmt) => B


// trick:
  rule replaceIsNotModifiedBy(B:Bool, true) => true

  rule replaceIsNotModifiedBy(B:Bool, false) => false

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

/*@
   Extend the substitution to specific expressions:
*/

  rule (I:Id isNotModifiedBy S:Stmt) [E:K / V:K] => I isNotModifiedBy S  [anywhere]

  rule B:Bool impliesBool true => true  [anywhere]

  rule B:Bool impliesBool B => true  [anywhere]

  rule (B:Bool andBool B':Bool) impliesBool B => true  [anywhere]
  rule (B':Bool andBool B:Bool) impliesBool B => true  [anywhere]

  rule B:Bool andBool true => B  [anywhere]

  rule true andBool B:Bool => B  [anywhere]

  rule B:Bool andBool B => B  [anywhere]

  rule (B1:Bool andBool B:Bool) andBool B => B1 andBool B  [anywhere]

  rule B:Bool orBool true => true  [anywhere]

  rule true orBool B:Bool => true  [anywhere]

  rule B:Bool impliesBool B => true [anywhere]

  // SExp (Streams)

  rule <k> X:Id :- S:Stmt => . ...</k>
       <env>... . => X |-> S ...</env>

  rule <k> (I:Int => .) :: S:Stmt ...</k>
       <env>... O |-> (_ => I)  ...</env>
       <observers> ListItem(O:Id) </observers>

  rule .K :: S:Stmt => S

  rule getSubstMap((M1:Map X:Id |-> S:Stmt), M2:Map)
       =>
       getSubstMap(M1, M2) 

  rule getSubst(X:K :: S1:K, X:K :: S2:K, M:Map) => getSubst(S1, S2, M)

  rule eqEnv((X:Id |-> S:Stmt Env1:Map), Env2:Map) => eqEnv(Env1, Env2) 

endmodule
