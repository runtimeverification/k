
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

  rule 'isInt(I1:Int +Int I2:Int) => true [anywhere]
  rule 'isInt(I1:Int *Int I2:Int) => true [anywhere] 
  rule 'isInt(I1:Int /Int I2:Int) => true [anywhere]

//@ Some simplification rules.

  rule (I:Int ==Int I:Int) => true [anywhere]

  rule (I:Int *Int I +Int I +Int I +Int 1)
       => 
       (I +Int 1) *Int (I +Int 1)
       [anywhere]

endmodule


//@ \section{Syntax}

module IMP-SYNTAX
  imports BUILTIN-SYNTAX-HOOKS
  imports SYMBOLIC-CALCULUS-SYNTAX

/*@
  This is the syntax of IMP, where we added the multiplication operator.
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

  syntax EqvPgm ::= "program1:" Pgm "program2:" Pgm "observers:" Ids ";"

  syntax Start ::= EqvPgm  


endmodule



//@ \section{Semantics}

module IMP
  imports IMP-SYNTAX
  imports SYMBOLIC-CALCULUS

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
  hypothesis only when in the k cell we have a main statement like while, if, 
  or assignment. 
*/

  syntax K ::= "storeHypo" "(" K ")"


/*@
  The semantics of the expressions remains unchanged.
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
  The semantics for memory lookup, skip, assignment, sequential composition,
  and if remain unchanged, too. The rules for assignment and if are annotated
  as transition for tracing reasons.
*/

  rule [lookup] :      <k> X:Id => I:Int ...</k>
                      <env>... X |-> I ...</env> 
  rule [skip] : skip => .

  rule [assignment]:
       <k> X:Id := I:Int => . ...</k>
       <env>... X |-> (_ => I) ...</env>
       [transition]

  rule [sequential] : S1;S2 => S1 ~> S2 [structural]

  rule [if-true] : if true  then S:Stmt else _ => S
       [transition]

  rule [if-false]: if false then _ else S:Stmt => S
       [transition]

/*@ 
    The rule for while is annotated as transition for technical reasons: since
  our formula uses while as the main statement, it forces to apply the rules
  for hypotheses before firing the semantic rule (if any).\\
  Moreover, the semantics of while is changed such each time in the cell k 
  we have an while , we store the hypotheses provided that the corresponding
  formula is included in the observational equivalence.
*/

  rule [while] :
       <k>
          while B:BExp do S:Stmt ~> K:K
          => 
          storeHypo(while B do S ~> K) ~>
          if B then S ; while B do S else skip ~> K
       </k> 
       [transition]



/*@
  \subsection{Additional Rules}
  The first two additional rules implement our approach for handling the symbolic
  boolean expressions. An elementary symbolic boolean expression (remember that 
  the boolean operators are strict in at leat one argument) is seen as a 
  variable and consequently its value is stored in the \texttt{env} cell.
  Each time a new elementary symbolic boolean expression is met, the current task 
  is split in two task: one for the \texttt{true} value, and the other one for
  the \texttt{false} value.\\
  In fact, we guess that this is the only rule that uses unification for computing
  the derivatives. More details will be added later.
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
         C:Bag
       </task>
       =>
       <task>
         <config>
           <k> true ~> K1 </k>
           <env> Rho1:Map (B |-> true) </env>
         </config>
         <config>
           <k> K2 </k>
           <env> Rho2:Map (B |-> true) </env>
         </config>
         C
       </task>
       <task>
         <config>
           <k> false ~> K1 </k>
           <env> Rho1:Map (B |-> false) </env>
         </config>
         <config>
           <k> K2 </k>
           <env> Rho2:Map (B |-> false) </env>
         </config>
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
         C:Bag
       </task>
       =>
       success)
       <observers> Obs:List </observers>
       when eqObs(<env> Env </env> 
                  <env> Env' </env>
                  <observers> Obs </observers>)
            ==K true


/*@
  The observational equivalence relation is defined by checking the equality of
  the observer variables in the two configurations (see how \texttt{eqObs} is 
  called.
*/

  syntax Bool ::= "eqObs" "(" Bag ")" [function]

  rule eqObs(<env> _ </env>
             <env> _ </env>
             <observers> .List </observers>)
       =>
       true
       [anywhere]

  rule eqObs( <env>... X:Id |-> V1:K ...</env>
              <env>... X |-> V2:K ...</env>
              <observers> ListItem(X) => . ...</observers> )
       when V1 ==K V2
       [anywhere]

  rule eqObs( <env>... X:Id |-> V1:K ...</env>
              <env>... X |-> V2:K ...</env>
              <observers> ListItem(X) ...</observers> )
       =>
       false
       when V1 =/=K V2
       [anywhere]
 
/*@
  The next rule gives semantics to the new construct \texttt{storeHyp}, which 
  consists of storing the hypothesis given by the arguments. Its semantics
  is similar to that of threads synchronization.
*/


  rule [store-hypo] :
       <task>
         <config> 
           <k> storeHypo(K1:K) => . ...</k>
           <env> Env1:Map </env>
         </config> 
         <config> 
           <k> storeHypo(K2:K) => . ...</k>
           <env> Env2:Map </env>
         </config>
         <formula> F:Bool </formula>
       </task>
       <hypos>... 
         .
         =>
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
       ...</hypos>
         <observers> Obs:List </observers>
       when eqObs(<env> Env1 </env> 
                  <env> Env2 </env> 
                  <observers> Obs </observers>)
            ==K true
/*@
  The next rule is intended to implement the entailment between the collected
  hypotheses and goals. Obviously, this is a partial implementation. Again,
  the formulas are ignored for now, because they are considered equal.
*/

  rule [circularity] :
       (<task>
         <config> 
           <k> K1:K </k>
           <env> Env1:Map </env>
         </config> 
         <config> 
           <k> K2:K </k>
           <env> Env2:Map </env>
         </config>
         <formula> F:Bool </formula>
       </task>
       =>
       success)
       <hypos>... 
         <hypo>
           <patt1> 
             <k1> K1 </k1>
             <env1> Env1':Map </env1>
           </patt1> 
           <patt2> 
             <k2> K2 </k2>
             <env2> Env2':Map </env2>
           </patt2>
           <formula> F </formula>
         </hypo>
       ...</hypos>
       <observers> Obs </observers>
     when eqObs(<env> Env1 </env> 
                <env> Env2 </env>
                <observers> Obs </observers> )


/*@
  The following rule creates the initial configuration from the equivalence
  specification given as input.
*/

  rule [initial] :
       <config>
         <k> 
           program1: P1:Pgm program2: P2:Pgm observers: Obs:Ids ;
           =>
           initVal(Obs) ~> P1
         </k>
         <env> _ </env>
       </config>
      (. =>
       <config>
         <k> 
           initVal(Obs) ~> P2
         </k>
         <env> . </env>
       </config>)
       <observers> . => Ids2List(Obs) </observers>

/*@
  The auxiliary construct \texttt{initVal()} is used for initializing the 
  observer variables with the same values in the two initial program
  configurations. 
*/

  syntax K ::= "initVal" "(" Ids ")"

  rule <k> initVal(.Ids) => . ...</k>
       <k> initVal(.Ids) => . ...</k>
       [structural]

  rule <config>
         <k> initVal((X:Id, Xs:Ids) => Xs) ...</k>
         <env>... . => X |-> symInt(fresh(I)) ...</env>
       </config> 
       <config> 
         <k> initVal((X:Id, Xs:Ids) => Xs) ...</k>
         <env>... . => X |-> symInt(fresh(I)) ...</env>
       </config> 
       <nextSymvar> I:Int => I +Int 1 </nextSymVar>
       [structural]
/*@
  The following is a helper function that transform a list of
  identifiers into a builtin list, used for storing the observer
  variables into the cell \texttt{observers}.
*/ 
  syntax List ::= "Ids2List" "(" Ids ")" [function]
  rule Ids2List(.Ids) => .List [anywhere]
  rule Ids2List(X:Id, Xs:Ids) => ListItem(X) Ids2List(Xs)
       [anywhere]


endmodule
