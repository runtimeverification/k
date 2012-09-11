//require "../symbolic/symbolic-calculus.k"
require "builtins/symbolic-calculus.k"

/*!
\setlength{\parindent}{1em}
\title{IMP  with Symbolic Values}
\author{Dorel Lucanu (\texttt{dlucanu@info.uaic.ro} and Vlad Rusu (Vlad.Rusu@inria.fr)}
\organization{"Alexandru Ioan Cuza" University of Iasi, INRIA Lille}
*/

//@ \section{Syntax}

module IMPS-SYNTAX
  imports BUILTIN-SYNTAX-HOOKS
  imports SYMBOLIC-CALCULUS-SYNTAX
//  imports BOOL-SYMBOLIC
//  imports INT-SYMBOLIC

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
  				| "if" BExp "then" Stmt "else" Stmt [prefer, strict(1)]
  				| "while" BExp "do" Stmt
                                | "for" Id "from" AExp "to" AExp "do" Stmt
                                  [strict(2 3)] 
  				> Stmt ";" Stmt   [left]
  				| "(" Stmt ")"    [bracket]

  /*@
    Extending the statements with symbolic values:
   */

  syntax StmtSymbolic ::= "symStmt" "(" Id ")"
  
  syntax Stmt ::= StmtSymbolic

/*@
  The following expressions are used in conditions.
  If it is included in the definition of the language, then its declaration
  here is no longer necessary.
*/

  syntax BExp ::= AExp "==" AExp  [strict]

  //@ get if no effect
  syntax Bool ::= Id "isNotModifiedBy" Stmt 

/*@
  The symbolic programs are programs extended with conditions.
*/

  syntax Pgm ::= "var" Ids ";" Stmt
  syntax Stmt ::= "assert" "(" BExp ")" [strict]
  syntax Ids ::= List{Id, ","}

  syntax InitVal ::= Id "->" Int
  syntax InitVals ::= List{InitVal,","}

  syntax CfgSym ::= "<k>" Pgm "</k>"
                    "<env>" InitVals "</env>"
                     "<condition>"  BExp "</condition>"

  syntax Start ::= CfgSym  

endmodule

//@ \section{Semantics}

module IMPS
  imports IMPS-SYNTAX
  imports SYMBOLIC-CALCULUS


  configuration <T color="yellow"> 
                  <config>
                    <k color="green"> $PGM:CfgSym  </k>
                    <env color="red"> .Map </env>
                  </config>
                  <condition> true </condition>
                  <nextSymvar> 0 </nextSymVar>
                </T>

/*@
  The values are defined as for the original IMP, but note that now Int includes
  the symbolic integer expressions.
*/

  syntax KResult ::= Int | #Bool


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

/*@ 
  Equality of ints we additionally added:
*/

  rule [eq] : I1:Int == I2:Int => I1 ==Int I2


  rule [program-no-vars]: <k> var .Ids ; S:Stmt => S ...</k> [structural]


  rule [program-still-vars]:
           <k> var X:Id, Xs:Ids; S:Stmt => var Xs; S ...</k>
          <env> Rho:Map (. => X |-> 0) </env> when notBool(X in keys(Rho))

/*@
  The semantics for the initial statements remain unchanged, too. 
  However, most of the rules are annotated as transitions for tracing reasons.
*/

  rule [skip] : skip => .
       [structural]

  rule [sequential] : S1;S2 => S1 ~> S2 [structural]

  rule [if-true] : (if true  then S:Stmt else _) => S
       [transition]

  rule [if-false]: (if false then _ else S:Stmt) => S
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

/*@
  Semantics of the symbolic statements:
*/

  syntax Map ::= "execute" "(" Stmt "," Map ")" 

  rule [symbolic-stmt] : 
       <k> SS:StmtSymbolic => .  ...</k>
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
       <k> lookup(X:Id, execute(SS:StmtSymbolic, Rho:Map)) 
           => 
           lookup(X, Rho)
       ...</k>
       <condition> F:K </condition>
       when F impliesBool (X isNotModifiedBy SS)

  rule [lookup] :
       lookup(X:Id, (execute(SS:StmtSymbolic, Rho:Map) Rho':Map)) 
       => 
       lookup(X:Id, Rho:Map)
       when notBool(X in keys(Rho')) andBool (Rho' =/=Map .Map)

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
  additional rules that conservatively extend the definition
*/


  rule <k>
          B:BoolSymbolic
          =>
          checkSat(F andBool B) ~> checkSat(F andBool notBool B) ~> B
       ...</k>
       <condition> F:Bool </condition>
//       when isBoolSymbolic(B)


  // (F impliesBool B) andBool (F impliesBool notBool B)
  rule <k> sat ~> sat ~> B:BoolSymbolic => false ...</k>
       <condition> F:K => F andBool notBool B  </condition> [transition]

  rule <k> sat ~> sat ~> B:BoolSymbolic => true ...</k> 
       <condition> F:K => F andBool B  </condition> [transition]

  // the other two cases

   rule sat ~> unsat ~> B:BoolSymbolic => true  // F impliesBool B

   rule unsat ~> sat ~> B:BoolSymbolic => false // F impliesBool notBool B
   
   rule assert(true) => .
//   rule <k> (assert(false) ~> K)  => . </k>
   

/*@
  When an existing elementary symbolic boolean expression has to be evaluated,
  its value is read the cell \texttt{env}.
*/

  rule <k> B:K => V ...</k>
       <env>... B |-> V:Bool ...</env>
       when isBoolSymbolic(B)


/*@
  The following rule creates the initial configuration from the equivalence
  specification given as input.
*/

  rule [initial] :
       <config>
         <k> 
           <k> P:Pgm </k>
           <env> Inits1:InitVals </env>
           <condition> F:BExp </condition>
           =>
           setInitVal(Inits1) ~> P
         </k>
       ...</config>
  <condition> _ => injectForm(F) </condition>

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

  rule injectForm(A1:AExp <= A2:AExp)
       =>
       injectAExp(A1)  <=Int injectAExp(A2)
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

  rule injectForm(true) => true [anywhere]
  rule injectForm(false) => false [anywhere]

//@ rules that translate the locally defined predicates to SMTLIB

  rule collectConstants( X:Id isNotModifiedBy S:Stmt ) => .Set [anywhere]
  rule Smtlib( X:Id isNotModifiedBy S:Stmt ) => "" [anywhere]

endmodule

