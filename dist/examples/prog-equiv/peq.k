require "modules/substitution.k"


/*!
\setlength{\parindent}{1em}
\title{IMP++}
\author{Dorel Lucanu (\texttt{grosu@illinois.edu}) and Vlad Rusu (Vlad.Rusu@inria.fr)}
\organization{"Alexandru Ioan Cuza" University of Iasi, INRIA Lille}
*/

//@ \section{Symbolic Calculus}

module SYMBOLIC-CALCULUS-SYNTAX

/*@ 
  The symbolic values needed to define the initial configuration.
  They are corresponding to the vriables in equivalence formula.
*/


  syntax IntSymVar ::= "symInt" "(" Id ")" 

/*@ 
  The following function is used to generate fresh names for symbolic values.
*/
  syntax Id ::= "fresh" "(" Int ")" [function] 
  rule fresh(I:Int) => String2Id("symVar" +String Int2String(I)) [anywhere]

/*@
  Any symbolic variable is of sort Int:
*/

  syntax Int ::= IntSymVar

endmodule

module SYMBOLIC-CALCULUS
  imports SYMBOLIC-CALCULUS-SYNTAX
  imports SUBSTITUTION

/*@
  This module is designed with a minimal support. 
*/



/*@
  The predicate defining the symbolic boolean expressions.
*/

  syntax Bool ::=  "isBoolSymExp" "(" K ")"


  rule isBoolSymExp(I1:Int <=Int I2:Int) => true
       when isIntSymExp(I1) ==K true
       [anywhere]

  rule isBoolSymExp(I1:Int <=Int I2:Int) => true
       when isIntSymExp(I2) ==K true
       [anywhere]

  rule isBoolSymExp(I1:Int ==Int I2:Int) => true
       when isIntSymExp(I1) ==K true
       [anywhere]

  rule isBoolSymExp(I1:Int ==Int I2:Int) => true
       when isIntSymExp(I2) ==K true
       [anywhere]

  rule isBoolSymExp(B1:Bool andBool I2:Bool) => true
       when isBoolSymExp(B1) ==K true
       [anywhere]

  rule isBoolSymExp(B1:Bool orBool I2:Bool) => true
       when isBoolSymExp(B1) ==K true
       [anywhere]
/*@ 
  \textbf{Remark.~~}
  The symbolic boolean expressions are not sobsorted to Bool.
  This is a trick that help us to handle easier this expressions.
*/

/*
  rule 'isBool(K:K) => true
       when isBoolSymExp(K) ==K true
       [anywhere]
*/

/*@
  The predicate defining the symbolic integer expressions.
*/
  syntax Bool ::= "isIntSymExp" "(" K ")" 
 
  rule isIntSymExp(I1:Int +Int I2:Int) => true
       when isIntSymExp(I1) ==K true
       [anywhere]

  rule isIntSymExp(I1:Int +Int I2:Int) => true
       when isIntSymExp(I2) ==K true
       [anywhere]

 
  rule isIntSymExp(I1:Int -Int I2:Int) => true
       when isIntSymExp(I1) ==K true
       [anywhere]

  rule isIntSymExp(I1:Int -Int I2:Int) => true
       when isIntSymExp(I2) ==K true
       [anywhere]

  rule isIntSymExp(I1:Int *Int I2:Int) => true
       when isIntSymExp(I1) ==K true
       [anywhere]

  rule isIntSymExp(I1:Int *Int I2:Int) => true
       when isIntSymExp(I2) ==K true
       [anywhere]

  rule isIntSymExp(I1:Int /Int I2:Int) => true
       when isIntSymExp(I1) ==K true
       [anywhere]

  rule isIntSymExp(I1:Int /Int I2:Int) => true
       when isIntSymExp(I2) ==K true
       [anywhere]


  rule isIntSymExp(K:K) => true
       when 'isIntSymVar(K) ==K true
       [anywhere]

/*@
  Extending Int with symbolic expressions:
*/
  rule 'isInt(K:K) => true
       when isIntSymExp(K) ==K true
       [anywhere]

  rule 'isInt(_:Int +Int _:Int) => true [anywhere]
  rule 'isInt(_:Int *Int _:Int) => true [anywhere] 
  rule 'isInt(_:Int /Int _:Int) => true [anywhere]

/*@
  The following rules extends the substitution to the symbolic values and
  symbolic expressions.
*/

  rule (F1:K andBool F2:K) [ V:K / X:K ]
        =>
        F1 [ V:K / X:K ] andBool F2[ V:K / X:K ]
        [anywhere]

  rule (I1:Int <=Int I2:Int) [ E1:K / E2:K ]
       =>
       (I1 [ E1 /E2 ]) <=Int (I2 [ E1 / E2 ])
       [anywhere]

  rule (I1:Int ==Int I2:Int) [ E1:K / E2:K ]
       =>
       (I1 [ E1 /E2 ]) ==Int (I2 [ E1 / E2 ])
       [anywhere]

  rule (I1:Int +Int I2:Int) [ E1:K / E2:K ]
       =>
       (I1 [ E1 /E2 ]) +Int (I2 [ E1 / E2 ])
       [anywhere]

  rule (I1:Int *Int I2:Int) [ E1:K / E2:K ]
       =>
       (I1 [ E1 /E2 ]) *Int (I2 [ E1 / E2 ])
       [anywhere]

  rule I:Int [ E1:K / E2:K ] => E1 
       when I ==K E2
       [anywhere]
 
  rule I:Int [ E1:K / E2:K ] => I
       when I =/=K E2
       [anywhere]

//@ Some simplification rules.

  rule (I:Int ==Int I:Int) => true [anywhere]

  rule (I:Int *Int I +Int I +Int I +Int 1)
       => 
       (I +Int 1) *Int (I +Int 1)
       [anywhere]

//@ The following is specific to the example wit sum of squares

  rule ((I1:Int ==Int I2:Int *Int I2) andBool (I3:Int ==Int I2))
       impliesBool
       ((I:Int +Int I1) ==Int (I +Int I3 *Int I3))
       =>
       true
       [anywhere]

  rule B:K impliesBool true => true  [anywhere]

  rule (B:K andBool B':K) impliesBool B => true  [anywhere]

  rule B:K andBool true => B  [anywhere]

  rule true andBool B:K => B  [anywhere]

  rule B:K orBool true => true  [anywhere]

  rule true orBool B:K => true  [anywhere]

  rule V1:K ==K V2:K impliesBool V1 ==K V2 => true [anywhere]

endmodule


//@ \section{Syntax}

module IMP-SYNTAX
  imports BUILTIN-SYNTAX-HOOKS
  imports SYMBOLIC-CALCULUS
//  imports SYMBOLIC-CALCULUS-SYNTAX

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
                                  [strict(2 3)] 
//                                | Id ":" "while" BExp "do" Stmt
//                                | Id ":" "for" Id "from" AExp "to" AExp "do" Stmt
//                                  [strict(3 4)] 
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


  syntax InitVal ::= Id "->" Int
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
  The following expression is used in conditions.
  If it is included in the definition of the language, then its declaration
  here is no longer necessary.
*/

  syntax BExp ::= AExp "==" AExp  [strict]

//@ get if no effect
  syntax Bool ::= Id "isNotModifiedBy" Stmt 

  /*@
    Extending the statements with symbolic values:
   */

  syntax StmtSymVar ::= "symStmt" "(" Id ")"
  
  syntax Stmt ::= StmtSymVar


endmodule

//@ \section{Semantics}

module PEQ
  imports IMP-SYNTAX
//  imports SYMBOLIC-CALCULUS

/*@
  A configuration is a multiset of tasks. Each task consists of an
  equivalence formula. The patterns are stored into a \texttt{config}
  cell and the condition in the \texttt{formula} cell.
  The cell \texttt{hypos} is for storing the hypotheses met during
  the proving process. It has a structure similar to that of tasks, but
  where the names of cells are changed in order to forbid the rules firing
  for hypotheses, in this way the hypotheses are kept unchanged. 
  The cell \texttt{observers} stores the list of the observer variables.
  The cell \texttt{nextSymVar} is used for generating fresh symbolic names.
*/

  configuration <T color="yellow"> 
                  <tasks> 
                    <task multiplicity="*">
                      <config multiplicity="*">
                        <k color="green"> $PGM:EqvPgm  </k>
                        <env color="red"> .Map </env>
                      </config>
                      <formula> true </formula>
                    </task>
                  </tasks>
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
                      <formula> true </formula>
                    </hypo>
                  </hypos>
                  <observers> .List </observers> 
                  <nextSymvar> 0 </nextSymVar>
                </T>

/*@
  The values are defined as for the original IMP, but note that now Int includes
  the symbolic integer expressions. Remember that the predicate \texttt{isBool} 
  is not extended to symbolic boolean expressions. So, the only boolean values 
  remain \texttt{true} and \texttt{false}.
*/

  syntax KResult ::= Int | Bool

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
       [transition]

  rule [if-false]: if false then _ else S:Stmt => S
       [transition]

  rule [while] :
          while B:BExp do S:Stmt 
          => 
          if B then S ; while B do S else skip
       [transition]

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

/*@
  The labelled recursive statements have a special semantics because
  the label must be propagated. Therefore we need a boolean function
  that discriminate between recursive and non-recursive statements.
*/

  syntax Boolean ::= "isRecursive" "(" Stmt ")" [function]
  rule isRecursive(while B:BExp do S:Stmt) => true [anywhere]
  rule isRecursive(for I:Id from A1:AExp to A2:AExp do S:Stmt) => true
       [anywhere]

/*@
  For the non-recursive statements, the labels are translated into 
  synchronyzing construct. Naturally, for these cases only the label
  is required for the synchronization. We prefer to save the whole
  content of the cell \texttt{k} as argument of the synchronyzing
*/

  rule <k>
          L:Id : S:Stmt ~> K:K
          =>
          storeHypo(L, S ~> K) ~> S
       </k>
       when isRecursive (S) =/=K true

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

  syntax Map ::= "execute" "(" Stmt "," Map ")" 

  rule [symbolic-stmt] : 
       <k> SS:StmtSymVar => .  ...</k>
       <env> M:Map => execute(SS, M) </env>
       [transition] 

/*@
  The memory lookup rule is changed because now the memory can be a 
  symbolic one obtained after a the execution of a symbolic statement.
*/

  syntax K ::= "lookup" "(" Id "," Map ")" [function]

  rule [lookup] : 
       <k> X:Id =>  lookup(X, Rho) ...</k>
       <env> Rho:Map </env> 

  rule [lookup] :  lookup(X:Id, (_ X |-> I:Int _)) => I

  rule [lookup] :
       <k> lookup(X:Id, execute(SS:StmtSymVar, Rho:Map)) 
           => 
           lookup(X, Rho)
       ...</k>
       <formula> F:K </formula>
       when F impliesBool (X isNotModifiedBy SS)

/*@
  The semantics of the assignment is modified because of the symbolic  
  statements.
*/

  syntax K ::= "update" "(" Id "," K ")"

  rule [assignment]:
       X:Id := I:Int
       => 
       update(X,I)
       [transition]

  rule [update]:
       <k> update(X:Id, V:K) => . ...</k>
       <env>... X |-> (_ => V) ...</env>
       [transition]

  rule [update]:
       <k> update(X:Id, V:K) => . ...</k>
       <env> (Rho:Map) (. => X |-> V) </env>
       when notBool(X in keys(Rho))
       [transition]

/*@
  \subsection{Additional Rules}
  The first two additional rules implement our approach for handling the symbolic
  boolean expressions. An elementary symbolic boolean expression (remember that 
  the boolean operators are strict in at leat one argument) is seen as a 
  variable and consequently its value is stored in the \texttt{env} cell.
  Each time a new elementary symbolic boolean expression is met, the current task 
  is split in two tasks: one for the \texttt{true} value, and the other one for
  the \texttt{false} value.\\
  In fact, we guess that this is the only rule that uses unification for computing
  the derivatives. 
  We assume that we have the formula:
  \begin{verbatim}
      <config>                            <config>
        <k> I1 <= I2 ~> K1 </k>     ~       <k> K2 </k>          if F
        <env> Rho1  </env>                  <env> Rho2 </env>
      </config>                           </config>
  \end{verbatim}
  The semantic rule evaluating \texttt{I1 <= I2}  is equivalent with the 
  following two rules:
  \begin{verbatim}
    rule I1 <= I2 => true when I1 <=Int I2
    rule I1 <= I2 => false when notBool(I1 <=Int I2)
  \end{verbatim} 
  Then the derivatives of the above goal are:
  \begin{verbatim}
      <config>                            <config>
        <k> true ~> K1 </k>       ~         <k> K2 </k>          if F andBool B
        <env> Rho1  </env>                  <env> Rho2 </env>
      </config>                           </config>
      <config>                            <config>
        <k> false ~> K1 </k>      ~         <k> K2 </k>          if F andBool 
        <env> Rho1  </env>                  <env> Rho2 </env>       notBool B
      </config>                           </config>
  \end{verbatim}
  Therefore the below rule can be interepreted as being the implementation of the
  [derive] rule from the proof system; it is a special case (and the only one)
  when the current goal has two derivatives.\\
  The values of the elementary symbolic boolean expressions are stored in the 
  cell \texttt{env} for efficiency reasons. Note that each such expression could
  have "synonims": e.g., if $B$ is $I_1\le I_2$ and $F$ implies $I_1=I'_1$, then
  $I'_1\le I_2$ is a synonim of $B$ and both of them have the same value.
*/

  rule <task>
         <config>
           <k> B:K ~> K1:K </k>
           <env> Rho1:Map  </env>
         </config>
         <config>
           <k> K2:K </k>
           <env> Rho2:Map </env>
         </config>
         <formula> F:K </formula>
         C:Bag
       </task>
       =>
       <task>
         <config>
           <k> storeSyns(F, B, true) ~> true ~> K1 </k>
           <env> Rho1:Map (B |-> true) </env>
         </config>
         <config>
           <k> K2 </k>
           <env> Rho2:Map (B |-> true) </env>
         </config>
         <formula> F andBool B  </formula>
         C
       </task>
       <task>
         <config>
           <k> storeSyns(F, B, false) ~> false ~> K1 </k>
           <env> Rho1:Map (B |-> false) </env>
         </config>
         <config>
           <k> K2 </k>
           <env> Rho2:Map (B |-> false) </env>
         </config>
         <formula> F andBool notBool (B) </formula>
         C
       </task>
       when isBoolSymExp(B)
            andBool notBool(B in keys(Rho1))
            andBool notBool(B in keys(Rho2))

/*@
  When an existing elementary symbolic boolean expression has to be evaluated, its
  value is read the cell \texttt{env}.
*/

  rule <k> B:K => V ...</k>
       <env>... B |-> V:Bool ...</env>
       when isBoolSymExp(B)


/*@
  The following rules remove an inconsistent formula, where the
  condition is false. Note that the stored symbolic boolean expressions
  are parts of the condition.
*/

  rule <task>...
         <env>... B |-> true B |-> false ...</env>
       ...</task>
       =>
       .
       when isBoolSymExp(B)

  rule <task>...
         <env>... B |-> true ...</env>
         <env>... B |-> false ...</env>
       ...</task>
       =>
       .
       when isBoolSymExp(B)

/*@
  The folowing rule "borrows" the value of a elementary boolean expression
  from the pairing configuration. Since these expressions includes symbolic
  values whose scopes are the entire formula, this rule is sound.
  Note also that only sysnonims are usually stored only in one environment.
*/

  rule <task>...
         <config>...
           <k> B:K => V ...</k>
           <env> Rho:Map </env>
         ...</config>
         <config>...
           <env>... B |-> V:Bool ...</env>
         </config>
       ...</task>
       when isBoolSymExp(B)
            andBool notBool (B in keys(Rho))

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

/*@
  The special bag \texttt{success} is used for removing tasks (goals).
*/

  syntax Bag ::= "success"

  rule success success => success 

/*@
  The next rule implements the basic entailment relation. The current version
  is incomplete because the formula is ignored (we tested only examples where
  the formula is true. We have to elaborate the implementation of the basic
  entailment.
*/

  rule [equality] :
       (<task>
         <config>
           <k> K:K </k>
           <env> Env:Map </env>
         </config>
         <config>
           <k> K </k>
           <env> Env':Map </env>
         </config>
         <formula> F:K </formula>
       </task>
       =>
       success)
       <observers> Obs:List </observers>
       when eqObs(<env> Env </env> 
                  <env> Env' </env>
                  <observers> Obs </observers>, F)
            ==K true


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
       [anywhere]

  rule eqObs( <env>... X:Id |-> V1:K ...</env>
              <env>... X |-> V2:K ...</env>
              <observers> ListItem(X) => . ...</observers>, F:K )
       when F impliesBool (V1 ==Int V2)
       [anywhere]

  rule eqObs( <env>... X:Id |-> V1:K ...</env>
              <env>... X |-> V2:K ...</env>
              <observers> ListItem(X) ...</observers> , F:K)
       =>
       false
       when  F impliesBool V1 =/=Int V2
       [anywhere]


/*@
  The next rule gives semantics to the new construct \texttt{storeHyp}, which 
  consists of storing the hypothesis given by the arguments. Its semantics
  is similar to that of threads synchronization.\\
  TBD: replace the values of the program variables with fresh symbolic
  values and add to formula the corresponding contraints.
/n-*/


  rule [store-hypo] :
       <task>
         <config> 
           <k> storeHypo(L:Id, K1:K) => . ...</k>
           <env> Env1:Map </env>
         </config> 
         <config> 
           <k> storeHypo(L, K2:K) => . ...</k>
           <env> Env2:Map </env>
         </config>
         <formula> F:K </formula>
       </task>
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
           <formula> F </formula>
         </hypo>
       </hypos>
       <observers> Obs:List </observers>
       when (eqObs(<env> Env1 </env> 
                  <env> Env2 </env> 
                  <observers> Obs </observers>, F) ==K true)
            andBool
            ((KItem(Hypos)
            |-subst
            KItem(<task>
               <config> 
                 <k> K1 </k>
                 <env> Env1 </env>
               </config> 
               <config> 
                 <k> K2 </k>
                 <env> Env2 </env>
               </config>
               <formula> F </formula>
             </task>))
             =/=K true)
       [transition]


  rule [store-hypo]:
       <task>
         <config> 
           <k> storeHypo(L:Id, K1:K) => . ...</k>
           <env> Env1:Map </env>
         </config> 
         <config> 
           <k> storeHypo(L, K2:K) => . ...</k>
           <env> Env2:Map </env>
         </config>
         <formula> F:K </formula>
       </task>
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
  The followings defines (special) cases when a current goal is a 
  consequence of the circular hypotheses.\\
  This relation must be more elaborated.
*/

  syntax K ::= "KItem" "(" Bag ")"
  syntax Bool ::= K "|-subst" K [function]

//rule KItem(<hypo> B1:Bag </hypo>) |-subst KItem(<task> B2:Bag </task>) => true [anywhere]


  rule KItem (H1:Bag H2:Bag) |-subst KItem(G:Bag)
       =>
       KItem (H1) |-subst KItem(G)
       orBool
       KItem (H2) |-subst KItem(G)
       when (KItem(H1) =/=K KItem(.Bag)) andBool (KItem(H2) =/=K KItem(.Bag))
       [anywhere]


  rule KItem(.Bag) |-subst KItem(G:Bag) => false [anywhere]

rule KItem(<hypo>      
       <formula>
         F:K
       </formula> 
       <patt1>        
         <k1>
          for I:Id from (A1:Int) to (A2:Int) do (S:Stmt) 
         </k1> 
         <env1>
          Rho1:Map
         </env1> 
       </patt1> 
       <patt2>        
         <k2> 
           (while (I <= A2) do (S ; (I := (I + 1)))) 
         </k2> 
         <env2>
          I |-> A1
          Rho2:Map
         </env2> 
       </patt2> 
     </hypo>) 

    |-subst

     KItem(<task>      
       <formula>
         F':K
       </formula> 
       <config>        
         <k>
          for I from A1':Int to A2 do S 
         </k> 
         <env>
          Rho1':Map
         </env> 
       </config> 
       <config>        
         <k> 
           (while (I <= A2) do (S ; (I := (I + 1)))) 
         </k>
         <env>
          I |-> A1'
          Rho2':Map
         </env>
       </config>
     </task>)
     => 
     true
     [anywhere]

rule KItem(<hypo>      
       <formula> F:K </formula> 
       <patt1>        
         <k1>
          while (I:Id <= N:Id) do ((S:Id := (S + (I * I))) ; (I := (I + 1))) 
         </k1> 
         <env1>          
           Rho1:Map
         </env1> 
       </patt1> 
       <patt2>        
         <k2>
           while (I <= N) do (((S := (S + K:Id)) ;
                              (K := (((K + I) + I) + 1))) ; 
                              (I := (I + 1))) 
         </k2> 
         <env2>          
           Rho2:Map
         </env2> 
       </patt2> 
     </hypo>)

     |-subst

     KItem(<task>      
       <formula> F':K </formula> 
       <config>        
         <k>
          while (I <= N) do ((S := (S + (I * I))) ; (I := (I + 1))) 
         </k> 
         <env>          
           Rho1':Map
         </env> 
       </config> 
       <config>        
         <k>
           while (I <= N) do (((S := (S + K:Id)) ;
                              (K := (((K + I) + I) + 1))) ; 
                              (I := (I + 1))) 
         </k> 
         <env>          
           Rho2':Map
         </env> 
       </config> 
     </task>)
     =>
     true
     [anywhere]

/*@
  The next rule is intended to implement the entailment between the collected
  hypotheses and goals. Obviously, this is a partial implementation. Again,
  the formulas are ignored for now, because they are considered equal.
*/

  rule [circularity] :
       (<task>
         <config> 
           <k> storeHypo(L:Id, K1:K) ...</k>
           <env> Env1:Map </env>
         </config> 
         <config> 
           <k> storeHypo(L, K2:K) ...</k>
           <env> Env2:Map </env>
         </config>
         <formula> F:K </formula>
       </task>
       =>
       success)
       <hypos> Hypos:Bag </hypos>
       when
       KItem(Hypos)
       |-subst 
       KItem(<task>
         <config> 
           <k> K1 </k>
           <env> Env1 </env>
         </config> 
         <config> 
           <k> K2 </k>
           <env> Env2 </env>
         </config>
         <formula> F </formula>
       </task>)
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
       <formula> _ => injectForm(F) </formula>
      (. =>
       <config>
         <k> 
           setInitValObs(Obs) ~> setInitVal(Inits2) ~> P2
         </k>
         <env> . </env>
       </config>)
       <observers> . => Ids2List(Obs) </observers>
//       <syncs> . => Strings2Set(Syncs) </syncs> 

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

  syntax K ::= "setInitValObs" "(" Ids ")"

  rule <k> setInitValObs(.Ids) => . ...</k>
       <k> setInitValObs(.Ids) => . ...</k>
       [structural]

  rule <config>
         <k> setInitValObs((X:Id, Xs:Ids) => Xs) ...</k>
         <env>... . => X |-> symInt(fresh(I)) ...</env>
       </config> 
       <config> 
         <k> setInitValObs((X:Id, Xs:Ids) => Xs) ...</k>
         <env>... . => X |-> symInt(fresh(I)) ...</env>
       </config> 
       <nextSymvar> I:Int => I +Int 1 </nextSymVar>
       [structural]

/*@ 
  The next function translates the initial formula into internal
  form.\\
  TBD: refactor it!!!!
*/


  syntax Bool ::= "injectForm" "(" BExp ")" [function]

  rule injectForm(A1:AExp == A2:AExp)
       =>
       injectAExp(A1)  ==Int injectAExp(A2)
       [anywhere]

  rule injectForm(B1:BExp and B2:BExp)
       =>
       injectForm(B1) andBool injectForm(B2)
       [anywhere]

  syntax Int ::= "injectAExp" "(" AExp ")" [function]
  rule injectAExp(I:Int) => I [anywhere]
  rule injectAExp(A1:AExp + A2:AExp)
       =>
       injectAExp(A1)  +Int injectAExp(A2)
       [anywhere]

  rule injectAExp(A1:AExp * A2:AExp)
       =>
       injectAExp(A1)  *Int injectAExp(A2)
       [anywhere]

  rule injectAExp(A1:AExp / A2:AExp)
       =>
       injectAExp(A1)  /Int injectAExp(A2)
       [anywhere]

  rule injectForm(X:Id isNotModifiedBy S:Stmt ) 
       =>
       X:Id isNotModifiedBy S:Stmt 
       [anywhere]

/*@
  The following is a helper function that transform a list of
  identifiers into a builtin list; it is used for storing the observer
  variables into the cell \texttt{observers}.
*/ 
  syntax List ::= "Ids2List" "(" Ids ")" [function]
  rule Ids2List(.Ids) => .List [anywhere]
  rule Ids2List(X:Id, Xs:Ids) => ListItem(X) Ids2List(Xs)
       [anywhere]

endmodule
