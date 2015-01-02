// Copyright (c) 2012-2015 K Team. All Rights Reserved.

require "builtins/symbolic-k.k"

/*!
\setlength{\parindent}{1em}

\newcommand{\IMP}{\textsc{imp}\xspace}
\newcommand{\STREAM}{\textsc{stream}\xspace}

\title{PEQ (Program Equivalence on \IMP)}
\author{Dorel Lucanu (\texttt{dlucanu@info.uaic.ro})}
\organization{Alexandru Ioan Cuza University of Ia\c{s}i, Romania}
\newcommand{\pattern}[2]{{#1}%
  \ifthenelse{\equal{#2}{}}{}{%
    \,{\pmb{\wedge}}\,{#2}%
  }%
}


*/

//@ \section{Syntax}

module IMP-SYNTAX

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


  syntax Stmt ::= "skip" // | Elt | Elt "::" Stmt | Id ":-" Stmt
                  | Id ":=" AExp   [strict(2)]
                  | "if" BExp "then" Stmt "else" Stmt [strict(1)]
                  | "while" BExp "do" Stmt
                                | "for" Id "from" AExp "to" AExp "do" Stmt
                                  [strict(2)]
                                | Id ":" Stmt
                  > Stmt ";" Stmt   [left]
                  | "(" Stmt ")"    [bracket]

  syntax Elt ::= Id | Int   // extension for streams
  syntax Stmt ::=  Elt // trebuie sa fie aici, altfel prgramul cicleaza!!!

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

  /*@
    Extending with symbolic values:
   */

  syntax Stmt ::= "#symStmt" "(" Id ")"  [onlyLabel, klabel(#symStmt)]

  syntax AExp ::= "#symAExp" "(" Id ")"  [onlyLabel, klabel(#symAExp)]

//  syntax Map ::= "#symMap" "(" Id ")" [onlyLabel, klabel(#symMap)]

  syntax Int ::= "#symInt" "(" Id ")" [onlyLabel, klabel(#symInt)]

endmodule


/*!
\setlength{\parindent}{1em}
\title{PEQ (Program Equivalence)}
\author{Dorel Lucanu (\texttt{dlucanu@info.uaic.ro}) and Vlad Rusu (Vlad.Rusu@inria.fr)}
\organization{"Alexandru Ioan Cuza" University of Iasi, INRIA Lille}
*/

//@ \section{Symbolic Maps}

module SYMBOLIC-DOMAIN
  imports IMP-SYNTAX

/*@ Matching Logic (ML) implication\\
This implication is used to test satisfaction relation between the circular hypothesis and
the current confuguration. Therefore we assume that it is of the form
$\pattern{\pi}{\phi}\implies \pattern{\pi'}{\phi'}$, where $\pattern{\pi}{\phi}$ will play
the role of the current configuration, and $\pattern{\pi'}{\phi'}$ the role of the
hypothesis. Further, we always assume that $\pattern{\pi'}{\phi'}$ is in abstract form,
i.e., of the form $(\exists X)\pattern{\overline{\pi}'}{\phi'\land \sigma}$,
where \emph{$\overline{\pi}$ is an abstraction of $\pi$ via $\sigma^\pi$}
(i.e., $\sigma^\pi(\overline{\pi})=\pi$), and $\sigma^\pi$ in the pattern condition is viewed
as a conjunction formula $\bigwedge x = \sigma^\pi(x)$ (the equality is in the symbolic
domain.\\
Since the current pattern condition is always satisfiable, the implication is equivalent to
$\phi\land \bigwedge\sigma\implies \phi'$, where $\sigma$ is the substitution that satisfies
$\sigma(\pi')=\sigma(pi)$ (we assume that the abstractions are defined such that such a
substitution always exists).

For the case of \IMP, we consider the abstractions defined such that
$X=\mathit{range}(M)$ with $M$ the content of the cell
\textsf{env}. We have
$\pattern{\kall{cfg}{\kall{k}{K}\kall{env}{M}}}{\phi}\implies
\pattern{\kall{cfg}{\kall{k}{K'}\kall{env}{M'}}}{\phi'}$
iff
$K = K'$ and
$\phi\land\bigwedge_{x\in\mathit{dom}(M')}(M'(x)=M(x))\implies \phi'$.
Note that for the equivalence formulas, $K$ and $K'$ are pairs of
programs and $M$ and $M"$ are pairs of maps. Since for the programs the
equality is required, only the maps and conditions are given as parameters.
*/

/*
  syntax Bool ::= impliesML(Map, Bool, Map, Bool) [function]

  rule impliesML(M:Map, F:Bool, M':Map, F':Bool) => true
       when checkSat((filter(F) andBool substMap2Bool(getSubstMap(M', M)))
                      andBool notBool(filter(F'))
                    ) ==K "unsat"

*/

  syntax Bool ::= impliesML(Map, Map, Bool, Map, Map, Bool) [function]

  rule impliesML(M1:Map, M2:Map, F:Bool, M1':Map, M2':Map, F':Bool) => true
       when checkSat(filter(F)
                      andBool substMap2Bool(getSubstMap(M1', M1))
                      andBool substMap2Bool(getSubstMap(M2', M2))
                      andBool notBool(filter(F'))
                    ) ==K "unsat"



/*@
  Compute the substitution given by the maps stored in the environments
*/

  syntax Map ::= "getSubstMap" "(" Map "," Map ")" [function]

  rule getSubstMap(.Map, M:Map) => .Map

  rule getSubstMap((M1:Map X:K |-> I:K), (M2:Map X |-> A:K))
       =>
       I |-> A getSubstMap(M1, M2)
       when isSymbolicInt(I) ==K true  // to be sure that M1 is abstract

  rule getSubstMap((M1:Map followup(S:Stmt, Env:Map, F:Bool)), M2:Map)
       =>
       getSubstMap(M1, M2)

  rule getSubstMap((#symbMap(IM:Id) M1:Map), M2:Map)
       =>
       getSubstMap(M1, M2)

/*
   translation of a map substitution into a boolean
*/
  syntax Bool ::= substMap2Bool(Map) [function]

  rule substMap2Bool(.Map) => true

  rule substMap2Bool(A:Int |-> B:Int) => A ==Int B

  rule substMap2Bool(A:Bool |-> B:Bool) => A ==Bool B

/*@
  Try to compute the substitution between two programs.
  The definition of \texttt{getSubst} depends on  the syntax of the language.
  Any extension of the language implies the update of this definition.
*/

  syntax Substitution ::= "getSubst" "(" K "," K ")" [function]
            |  K "replBy" K [strict]  // a substitution pair
            |  Substitution ";;" Substitution [left]      // concatenation of substitutions
            |  "emptySubst"

  rule getSubst(K:K, K) => emptySubst

  rule getSubst(A1:K + A1':K, A2:K + A2':K)
       =>
       getSubst(A1, A2) ;; getSubst(A1', A2')


  rule getSubst(A1:K * A1':K, A2:K * A2':K)
       =>
       getSubst(A1, A2) ;; getSubst(A1', A2')


  rule getSubst(A1:K / A1':K, A2:K / A2':K)
       =>
       getSubst(A1, A2) ;;  getSubst(A1', A2')


  rule getSubst(A1:K <= A1':K, A2:K <= A2':K)
       =>
       getSubst(A1, A2) ;; getSubst(A1', A2')


  rule getSubst(B1:K and B1':K, B2:K and B2':K)
       =>
       getSubst(B1, B2) ;; getSubst(B1', B2')


  rule getSubst(not B1:K, not B2:K) => getSubst(B1, B2)


  rule getSubst(S1:K ; S1':K, S2:K ; S2':K)
       =>
       getSubst(S1, S2) ;; getSubst(S1', S2')


  rule getSubst(if B1:K then S1:K else S2:K, if B1':K then S1':K else S2':K)
       =>
       getSubst(B1, B1') ;; getSubst(S1, S1') ;; getSubst(S2, S2')


  rule getSubst(while B:K do S:K, while B':K do S':K)
       =>
       getSubst(B, B') ;; getSubst(S, S')


  rule getSubst(for X:K from A1:K to A2:K do S:K,
                for X:K from A1':K to A2':K do S':K)
       =>
       getSubst(A1, A1') ;; getSubst(A2, A2') ;; getSubst(S, S')


  rule getSubst(X:K := A1:K, X := A2:K) => getSubst(A1, A2)


  rule getSubst(K1:K ~> K2:K, K1':K ~> K2':K)
       =>
       getSubst(K1, K1') ;; getSubst(K2, K2')
       when (K1 =/=K .K)
       andBool (K2 =/=K .K)
       andBool (K1' =/=K .K)
       andBool (K2' =/=K .K)

  rule getSubst(L1:Id : S1:K, L2:Id : S2:K) => getSubst(S1, S2)


  rule getSubst(X:Id, X:Id) => emptySubst

  rule getSubst(#symAExp(X:K), A:AExp) => (#symAExp(X) replBy A)

  rule getSubst(#symInt(X:K), A:AExp) => (#symInt(X) replBy A)

  rule getSubst(#symBExp(X:K), B:BExp) => (#symBExp(X) replBy B)

  rule getSubst(#symBool(X:K), B:BExp) => (#symBool(X) replBy B)


  // to be completed


/*@
  Check if a Map is a substitution (real map):
*/

  syntax Bool ::= "isSubst" "("  K ")"  [function]

 rule isSubst(S:K) => isRelation(S) andBool isAssocArray(S)

/*
  rule isSubst(emptySubst) => true

  rule isSubst(I:K replBy A:K) => true

  rule isSubst(M:K ;; (I:K replBy A:K)) => isSubst(M)
*/

  syntax K ::= "isRelation" "("  K ")"  [function]

  rule isRelation(emptySubst) => true

  rule isRelation(I:K replBy A:K) => true

  rule isRelation(Rest:K ;; (I:K replBy A:K)) => isRelation(Rest)

  syntax Bool ::= "isAssocArray" "("  K ")"  [function]

  rule isAssocArray(emptySubst) => true

  rule isAssocArray(I:K replBy A:K) => true

  rule isAssocArray(I:K replBy A:K ;; Rest:K) => isAssocArray(Rest)
       when isInDom(I, Rest) =/=K true

  rule isAssocArray(I:K replBy A:K ;; Rest:K) => isAssocArray(Rest)
       when isInDom(I, Rest) ==K true andBool valOf(I, Rest) ==K A

  syntax Bool ::= isInDom(K, K) [function]

  rule isInDom(X:K, emptySubst) => false


  rule isInDom(I:K, I replBy A:K) => true

  rule isInDom(I:K, (I replBy A:K ;; Rest:K)) => true

  rule isInDom(I:K, X replBy A:K) => false
       when I=/=K X

  rule isInDom(I:K, (X replBy A:K ;; Rest:K)) => isInDom(I,  Rest)
       when I=/=K X

  syntax KItem ::= valOf(K, K)

  rule valOf(I:K, I replBy A:K) => A

  rule valOf(I:K, (I replBy A:K ;; Rest:K)) => A

  rule valOf(I:K, (X replBy A:K ;; Rest:K)) => valOf(I,  Rest)
       when I=/=K X


 //@ Two auxiliary rules

  rule S:Substitution ;; emptySubst => S [anywhere]

  rule emptySubst ;; S:Substitution => S [anywhere]




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
       eqEnv(Env1, Env2, F)


  rule eqObs( <env>... X:Id |-> V1:Int ...</env>,
              <env>... X    |-> V2:Int ...</env>,
              <observers> ListItem(X) => . ...</observers>, F:K )
       when checkSat(filter(F) andBool notBool(V1 ==Int V2)) ==K "unsat"

/*@
  the equality of two (symbolic environments):
*/

  syntax Bool ::= "eqEnv" "(" Map "," Map "," Bool ")" [function]

  rule eqEnv(Env:Map, Env, _) => true

  rule eqEnv((X:K |-> V1:Int Env1:Map), (X |-> V2:Int Env2:Map), F:Bool)
       =>
       eqEnv(Env1, Env2, F)
       when checkSat(filter(F) andBool notBool(V1 ==Int V2)) ==K "unsat"

  rule eqEnv((X:K |-> V1:Bool Env1:Map), (X |-> V2:Bool Env2:Map), F:Bool)
       =>
       eqEnv(Env1, Env2, F)
       when checkSat(filter(F) andBool notBool(V1 ==Bool V2)) ==K "unsat"

  rule eqEnv((X:K |-> V:K Env1:Map), (X |-> V Env2:Map), F:Bool)
       =>
       eqEnv(Env1, Env2, F)

  rule eqEnv(followup(S:Stmt, Env1:Map, F1:Bool),
             followup(S:Stmt, Env2:Map, F2:Bool), F:Bool)
       =>
       eqEnv(Env1, Env2, F1)
       andBool checkSat(filter((F1 andBool notBool F2) orBool
                        (F2 andBool notBool F1)))
               ==K "unsat"

 //@ An auxiliary rule for maps:

  rule MI:MapItem MI => MI [anywhere]



/*@
  isNotModifiedBy
*/
  syntax Bool ::= K "isNotModifiedBy" K

  rule X:Int isNotModifiedBy _:K => true when isSymbolicInt(X) [anywhere]
  rule X:Bool isNotModifiedBy _:K => true when isSymbolicBool(X)  [anywhere]

  syntax Map ::= "followup" "(" K "," Map "," Bool ")"
  rule isSymbolicMap(followup(_:K, _:Map, _:Bool)) => true [anywhere]


// in the following, "myImpliesBool" should be removed when we shall have
  // a complete implementation of Bool


  rule followup(S:K, (X:K |-> V:K M:Map), F:Bool)
       =>
       X |-> V followup(S, M, F)
       when (F myImpliesBool (X isNotModifiedBy S))
       [anywhere]

// temporary solution until the correct sorting of #symMap() is solved

  syntax Map ::= "#symbMap" "(" Id ")"
  rule isSymbolicMap(#symbMap(_:Id)) => true [anywhere]

  //@ Extend keys()
  rule keys ((followup(SS:K, Rho:Map, F:Bool) => .) _)
  rule keys ((#symbMap(_) => .) _)

  //@ Lookup
  syntax K ::= "lookup" "(" K "," Map ")" [function]
  rule [lookup] :  lookup(X:K, (_ X |-> V:K _)) => V

  //@ Update
  syntax Map ::= "update" "(" Map "," K "," K ")" [function]

  rule [update]:
       update((M:Map X:K |-> _), X, V:K) => (M X |-> V)

  rule [update]:
       update(M:Map, X:K, V:K) => (M X |-> V)
       when notBool(X in keys(M))


/*@
  Helper functions that are used for cleaning a formula before sending it
  to the SMT solver.
*/

  rule K2SMTLib(X:K isNotModifiedBy S:K) => "true" [anywhere] // doesn't work

  // the following will be removed when K2SMTLib is fixed

  syntax Bool ::= "filter" "(" Bool ")" [function]
               |  "replaceIsNotModifiedBy" "(" Bool "," Bool ")" [function]

  rule replaceIsNotModifiedBy(B:Bool, X:K isNotModifiedBy S:K) => B

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


// rule filter(B:Bool) => B

/*@
  The following defines the substitution of the symbolic values with
  symbolic expressions.
*/

  syntax K ::= K "[" K "/" K "]" [function]

  rule B:K [ V:K / X:K ] => replace(X, V, B)

  //@ Replace X:K by V:K in E:K

  syntax K ::= replace(K,K,K) [function]
  syntax KList ::= replaceList(K,K,KList) [function]
  syntax KList ::= replaceListList(KList,K,KList) [function]

  rule replace(X:K, V:K, X) => V
  rule replace(XL:KLabel(XKL:KList), V:K, EL:KLabel(EKL:KList))
        =>
       EL(replaceList(XL(XKL), V, EKL))  when XL =/=KLabel EL
  rule replace(XL:KLabel(XKL:KList), V:K, XL:KLabel(EKL:KList))
        =>
        XL(replaceListList(XKL, V, EKL))

  rule replaceList(X:K, V:K, .KList) => .KList
  rule replaceList(X:K, V:K, (E:K,, EKL:KList))
       =>
       replace(X, V, E),, replaceList(X, V, EKL)

  rule replaceListList(.KList, V:K, EKL:KList) => EKL
  rule replaceListList((X:K,, XKL:KList), V:K, (E:K,, EKL:KList))
       =>
       replace(X, V, E),, replaceListList(XKL, V, EKL)

/*
  A temporary solution until the buitin operations on Bool will be completely
  defined.
*/


  syntax Bool ::= Bool "myImpliesBool" Bool


  rule B:Bool myImpliesBool true => true  [anywhere]

  rule B:Bool myImpliesBool B => true  [anywhere]


  rule (B1:Bool andBool B2:Bool) myImpliesBool B:Bool => true
       when B1 myImpliesBool B
       [anywhere]

  rule (B1:Bool andBool B2:Bool) myImpliesBool B:Bool => true
       when B2 myImpliesBool B
       [anywhere]

  rule (B:Bool andBool B':Bool) myImpliesBool B => true  [anywhere]
  rule (B':Bool andBool B:Bool) myImpliesBool B => true  [anywhere]

 // the following rules are ignored by the current compiler

  rule B:Bool andBool true => B  [anywhere]

  rule true andBool B:Bool => B  [anywhere]

  rule B:Bool andBool B => B  [anywhere]

  rule (B1:Bool andBool B:Bool) andBool B => B1 andBool B  [anywhere]

  rule B:Bool orBool true => true  [anywhere]

  rule true orBool B:Bool => true  [anywhere]

endmodule



//@ \section{Semantics}

module PEQ
  imports SYMBOLIC-DOMAIN


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
                      <cash-env> .Map </cash-env>
                    </goal>
                  </goals>
//          <output stream="stdout"> ListItem("Proving ...\n") </output>
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
  syntax Val ::= Int | #Bool

/*@
  We use a new syntactic construct that help us to store hypotheses. The basic
  idea is to add the hypotheses in a controlled way. For instance, we may add
  hypothesis only when on the top in the two k cells we have  statement with
  the same label (the label is a kind of "rendevous" synchronisarion).
*/

  syntax KItem ::= "storeHypo" "(" K ")"   // for storing hypotheses
                |  "lbldStmt" "(" Id "," K ")"    // event signalling a labelled
                                                  // statement

                |  "checkHypo" "(" K "," Map "," K "," Map "," HyposCellFragment ")"
                   // for checking hypotheses one by one

                |  "checkCond" "(" K "," K ")"  // check the conditions of the
                                     // current formula and checked hypothesis

  syntax KItem ::= "break"  // to temporarily stop one of the two programs

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
       [transition]


/*@ \subsection{Labelled statements}
  We first extend the contextual declarations (derived from the strictness
  attribute) to the labelled transitions.
*/

  context L:Id : for _:Id from HOLE to _:AExp do _:Stmt
  context L:Id : if HOLE then _:Stmt else _:Stmt


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
       [transition]

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
       <condition> F:Bool </condition>
       when (notBool #symAExp(XS) in keys(Rho)
             andBool eqEnv(Rho, Rho', F) ==K true)
            andBool fresh(VS:Int)
//       [transition]

  rule [symbolic-aexp] :
       <config>...
         <k> #symAExp(XS:K) =>  VS ...</k>
         <env> Rho:Map => update(Rho, #symAExp(XS), VS) </env>
       ...</config>
       <config>...
         <env> Rho':Map </env>
       ...</config>
       <condition> F:Bool </condition>
       when (notBool #symAExp(XS) in keys(Rho)
             andBool eqEnv(Rho, Rho', F) =/=K true)
            andBool fresh(VS:Int)

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
         <cash-env> KB:Map </cash-env>
         C:Bag
       </goal>
       =>
       <goal>
         <config>
           <k> storeSyns(F, B, true) ~> true ~> K1 </k>
           <env> Rho1 </env>
         </config>
         <condition> F andBool B  </condition>
         <cash-env> KB:Map (B |-> true) </cash-env>
         C
       </goal>
       <goal>
         <config>
           <k> storeSyns(F, B, false) ~> false ~> K1 </k>
           <env> Rho1 </env>
         </config>
         <condition> F andBool notBool (B) </condition>
         <cash-env> KB:Map (B |-> false) </cash-env>
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
  its value is read the cell \texttt{kb}.
*/

  rule <k> B:K => V ...</k>
       <cash-env>... B |-> V:Bool ...</cash-env>
       when isSymbolicBool(B)


/*@
  The following rules remove an inconsistent formula, where the
  condition is false. Note that the stored symbolic boolean expressions
  are parts of the condition.
*/

  rule <goal>...
         <cash-env>... B:K |-> true B |-> false ...</cash-env>
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



  /*@
    Store the elementary symbolic boolean expressions obtained as
    "synonims" of the already stored ones due to the path formula
  */

  syntax KItem ::= "storeSyns" "(" K "," K "," Bool ")"

  rule storeSyns(F1:K andBool F2:K, B:K, V:Bool)
       =>
       storeSyns(F1, B, V) ~> storeSyns(F2, B, V)

  rule <k> storeSyns(I1:Int ==Int I2:Int, B:K, V:Bool) => . ...</k>
       <cash-env>... . => (B[I1/I2] |-> V) ...</cash-env>
       when B[I1/I2] =/=K B

  rule <k> storeSyns(I1:Int ==Int I2:Int, B:K, V:Bool) => . ...</k>
       <cash-env>... . => (B[I2/I1] |-> V) ...</cash-env>
       when B[I2/I1] =/=K B

  rule storeSyns(I1:Int ==Int I2:Int, B:K, V:Bool) => .
       when (B[I1/I2] ==K B) andBool (B[I2/I1] ==K B)

  rule storeSyns(X:Id isNotModifiedBy S:Stmt, B:K, V:Bool) => .

  rule storeSyns(X:AExp isNotModifiedBy S:Stmt, B:K, V:Bool) => .

  rule storeSyns(X:BExp isNotModifiedBy S:Stmt, B:K, V:Bool) => .

  rule <k> storeSyns(I1:Int <=Int I2:Int, B:K, V:Bool) => . ...</k>

  rule <k> storeSyns(notBool(F:K), B:K, V:Bool) => . ...</k>

/*
  rule (<goals> .Bag </goals> => .)
       <output> _ => ListItem("true") </output>
*/

/*@
  The next rule implements the basic entailment relation. The current version
  is incomplete because we have to show it is sound on the tested (it is depending on
  hpw the observation relation is defined).
  We have to elaborate the implementation of the basic
  entailment.
*/

  rule [basic-entailment] :
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
         C:Bag
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
         C:Bag
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
           <k> checkHypo(K1:K, Env1:Map, K2:K, Env2:Map, .Bag)
                =>
                storeHypo(K1)
           ...</k>
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
       [transition]


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
  Since the configurations in the current formula are unordered, we have
  to check two cases.

  We consider two additional computational tasks:\\
  computeSubst(Substitution) - that evaluates the components of the given
  substitution in the current environment,\\
  hypoInfo(Bool, Map, Map) - that stores the info about the currently tested
  circular hypothesis; the condiition comoponent of the hypothesis is updated
  with the substitution given by the programs.
*/


  syntax KItem ::= computeSubst(Substitution)
                 | hypoInfo(Bool, Map, Map)

  rule computeSubst(X:K replBy E:K)
       =>
       X:K replBy E:K ~> computeSubst(emptySubst)
//       [transition]

  rule computeSubst(X:K replBy E:K ;; S:Substitution)
       =>
       X:K replBy E:K ~> computeSubst(S)
//       [transition]


  rule (X:Int replBy A:Int => .) ~> computeSubst(S:Substitution)
                                 ~> hypoInfo((F':Bool => F' [ A / X ]), _, _)
//       [transition]

  rule <k> (X:Int replBy A:Int => .) ~> computeSubst(S:Substitution) ...</k>
       <k>  computeSubst(S:Substitution) ~>
           hypoInfo((F':Bool => F' [ A / X ]), _, _)
       ...</k>
//       [transition]

  /*@
  First case: there is substitution between the current configuration
  <c1, c2> /\ F and the hypothesis <c1', c2'> /\ F' and the current configuration
  is included in the observational relation.
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
             computeSubst(getSubst(K1', K1)) ~> hypoInfo(F', Env1', Env2')
             ~> checkHypo(K1:K, Env1:Map, K2:K, Env2:Map, Hypos')
           ...</k>
           <env> _ => Env1 </env>
         ...</config>
         <config>
           <k> break => computeSubst(getSubst(K2', K2)) ~> break ...</k>
           <env> _ => Env2 </env>
         ...</config>
         <condition> F:K </condition>
       ...</goal>
       <observers> Obs:List </observers>
       when (eqObs(<env> Env1 </env>,
                   <env> Env2 </env>,
                   <observers> Obs </observers>, F) ==K true)
       andBool ((isSubst(getSubst(K1', K1)) ==K true)
                 andBool (isSubst(getSubst(K2', K2)) ==K true))
       [transition]
  /*@
  Second case: there is substitution between the current configuration
  <c1, c2> /\ F and the hypothesis <c2', c1'> /\ F' and the current configuration
  is included in the observational relation.
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
             computeSubst(getSubst(K2', K1)) ~> hypoInfo(F', Env2', Env1')
             ~> checkHypo(K1:K, Env1:Map, K2:K, Env2:Map, Hypos')
           ...</k>
           <env> _ => Env1 </env>
         ...</config>
         <config>
           <k> break => computeSubst(getSubst(K1', K2)) ~> break ...</k>
           <env> _ => Env2 </env>
         ...</config>
         <condition> F:K </condition>
       ...</goal>
       <observers> Obs:List </observers>
       when (eqObs(<env> Env1 </env>,
                   <env> Env2 </env>,
                   <observers> Obs </observers>, F) ==K true)
       andBool ((isSubst(getSubst(K1', K2)) ==K true)
                andBool (isSubst(getSubst(K2', K1)) ==K true))
       [transition]

/*@
  The case when an hypothesis does not match the current formula.
*/

  rule [check-hyp-fail] :
       <goal>
         <config>
           <k> checkHypo(K1, Env1, K2, Env2,
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
       when ((isSubst(getSubst(K1', K1)) =/=K true)
             orBool (isSubst(getSubst(K2', K2)) =/=K true)
            ) andBool
            ((isSubst(getSubst(K1', K2)) =/=K true)
             orBool (isSubst(getSubst(K2', K1)) =/=K true)
            )
       [transition]


  /*@ The case when the circularity rule can be applied. The goal is removed.
  */

  rule [circularity] :
       (<goal>
         <config>
           <k> computeSubst(emptySubst) ~>
               hypoInfo(F':Bool, Env1':Map, Env2':Map)
           ...</k>
           <env> Env1:Map </env>
         ...</config>
         <config>
           <k> computeSubst(emptySubst) ...</k>
           <env> Env2:Map </env>
         ...</config>
         <condition> F:Bool </condition>
         C:Bag
       </goal>
       =>
       .)
       when (impliesML(Env1, Env2, F, Env1', Env2', F')  ==K true)
       [transition]

  /*@ The case when the circularity rule cannot be applied. The next hypothesis
      is checked.
  */

  rule [circularity-fail] :
       <goal>
         <config>
           <k>
              computeSubst(emptySubst) ~> hypoInfo(F':Bool, Env1':Map, Env2':Map)
               =>
              .
           ...</k>
           <env> Env1:Map </env>
         ...</config>
         <config>
           <k> computeSubst(emptySubst) => . ...</k>
           <env> Env2:Map </env>
         ...</config>
         <condition> F:Bool </condition>
         C:Bag
       </goal>
       when (impliesML(Env1, Env2, F, Env1', Env2', F')  =/=K true)
       [transition]


  /*@ The rules preparing the storing of an hypothesis. The hypothesis is
  stored in abstract form.
  */
  rule [store-hypo] :
       <config>
         <k> storeHypo(K1:K) => getFresh(Env1) ~> restore(K1, Env1) ...</k>
         <env> Env1:Map </env>
       ...</config>
//       [transition]


  //@ Generates fresh symbolic values for the stored hypothesis
  syntax KItem ::= "getFresh" "(" Map ")"

  rule [getFresh] :
       <config>
         <k> getFresh(((X:Id |-> _:Int) => .) _ ) ...</k>
         <env>... X |-> (V:Int => VS) ...</env>
       ...</config>
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

  syntax KItem ::= "restore" "(" K "," Map ")"

  rule [restore] :
       <goal>
         <config>
           <k> restore(K1:K, Env1':Map) => . ...</k>
           <env> Env1:Map => Env1' </env>
         ...</config>
         <config>
           <k> restore(K2:K, Env2':Map) => . ...</k>
           <env> Env2:Map => Env2' </env>
         ...</config>
         <condition> F:Bool </condition>
       ...</goal>
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
         ...</config>
         <config>
           <k> lbldStmt(L2:Id, K2:K) => . ...</k>
           <env> Env2:Map </env>
         ...</config>
         <condition> F:K </condition>
       ...</goal>
       <observers> Obs:List </observers>
       when
       (L1 =/=K L2) orBool
       (eqObs(<env> Env1 </env>,
             <env> Env2 </env>,
             <observers> Obs </observers>, F) =/=K true)
//       [transition]

/*@
  The following rules are commented  because of the state explosion problem.
*/


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
       ...</goal>
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
       ...</goal>
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


  syntax KItem ::= "setInitVal" "(" InitVals ")"

  rule setInitVal(.InitVals) => .
       [structural]

  rule <k> setInitVal((X:Id -> V:Int, XVs:InitVals) => XVs) ...</k>
       <env>... . => X |-> V ...</env>
       [structural]

  rule <k> setInitVal((SymMap(M:Id), XVs:InitVals) => XVs) ...</k>
       <env>... . => #symbMap(M) ...</env>
       [structural]

  syntax KItem ::= "setInitValObs" "(" Ids ")"

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

  rule injectForm(X:AExp isNotModifiedBy S:Stmt )
       =>
       X isNotModifiedBy S

  rule injectForm(X:BExp isNotModifiedBy S:Stmt )
       =>
       X isNotModifiedBy S


/*@
  The following is a helper function that transform a list of
  identifiers into a builtin list; it is used for storing the observer
  variables into the cell \texttt{observers}.
*/
  syntax List ::= "Ids2List" "(" Ids ")" [function]
  rule Ids2List(.Ids) => .List
  rule Ids2List(X:Id, Xs:Ids) => ListItem(X) Ids2List(Xs)


//@ rules that translate the locally defined predicates to SMTLIB


// regula asta trebuie sa fie aici; daca se muta, programul cicleaza!!!!


  rule getSubstMap((M1:Map X:Id |-> S:Stmt), M2:Map)
       =>
       getSubstMap(M1, M2)

endmodule
