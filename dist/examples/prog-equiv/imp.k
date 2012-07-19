
//@ \section{Syntax}

module IMP-SYNTAX
  imports BUILTIN-SYNTAX-HOOKS 

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
  syntax Start ::= Pgm  

endmodule

//@  \section{Symbolic calculus}

module SYMBOLIC-CALCULUS

/*@
  This module is designed for our example. 
*/

//@ The variable used in the programs:

  syntax #Id ::= "i" | "n" | "s" | "k" 

/*@ 
  The symbolic values needed to define the initial configuration.
  They are corresponding to the vriables in equivalence formula.
*/

  syntax IntSymVar ::= "n0" | "s0" | "i0"

  syntax Int ::= IntSymVar

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

//@ \section{Semantics}

module IMP
  imports IMP-SYNTAX
  imports SYMBOLIC-CALCULUS

/*@
  A configuration is a multiset of tasks. Each task consists of an
  equivalence formula. The patterns are stored into a \texttt{config}
  cell and the condition in the \texttt{formula} cell.
*/

  configuration <T color="yellow"> 
                  <tasks> 
                    <task multiplicity="*">
                      <config multiplicity="*">
                        <k color="green"> .K  </k>
                        <env color="red"> .Map </env>
                      </config>
                      <formula> true </formula>
                      <guard> .Map </guard>
                    </task>
                  </tasks>
                </T>

/*@
  The values are defined as for the original IMP, but note that now Int includes
  the symbolic integer expressions. Remeber that the predicate \texttt{isBool} 
  is not extended to symbolic boolean expressions. So, the only boolean values 
  remain \texttt{true} and \texttt{false}.
*/

  syntax KResult ::= Int | Bool

// **********************

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
  and if remain unchanged, too. The rule for assignment is annotated
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

  rule [if-false]: if false then _ else S:Stmt => S

/*@ 
    The rule for while is annotated as transition for technical reasons: since
  our formula uses while as the main statement, it forces to apply the rules
  for hypotheses before firing the semantic rule (if any).
  From the same reasons, the execution of while changes the guard  such that
  the hypothesis added by the goal can be fired after that.
  We convetionally named our goal "sqsum".
*/

  syntax K ::= "sqsum"

  rule [while] :
       <k>
          while B:BExp do S:Stmt
          => 
          if B then S ; while B do S else skip
       ...</k>
       <guard>... sqsum |-> ( _ => true ) ...</guard> 
       [transition]



/*@
  \subsection{Additional Rules}
  The first two additional rules implement our trick for handling the symbolic
  boolean expressions. An elementary symbolic boolean expression (remember that 
  the boolean operators are strict in at leat one argument) is seen as a 
  variable and consequently its value is stored in the \texttt{env} cell.
  Each time a new elementary symbolic boolean expression is met, the current task 
  is split in two task: one for the \texttt{true} value, and the other one for
  the \texttt{false} value.
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
  The next rule implements the basic entailment relation. Two configurations
  are observational equivalent iff the values for the program variables \texttt{n},
  \texttt{s}, aand \texttt{i} are the same.
*/

  rule [equality] :
       <task>
         <config>
           <k> K:K </k>
           <env> n |-> N:Int s |-> S:Int i |-> I:Int Env:Map </env>
         </config>
         <config>
           <k> K </k>
           <env> n |-> N s |-> S i |-> I Env':Map </env>
         </config>
         C:Bag
       </task>
       =>
       success

/*@
  The next rule applies the hypothesis added by the initial processing
  of the goal:
*/

  rule [circularity-sqsum] :
            ( <task>
                <config>
                  <k> 
		    while (i <= n) do (
		      s := s + i * i;
		        i := i + 1
		    )
                  </k>
                  <env>
                       i |-> I1:Int
                       s |-> S1:Int 
                  ...</env>
                </config>
                <config>
                  <k>
	 	    while (i <= n) do (
		      s := s + k;
		        (k := k + i + i + 1;
		           i := i + 1)
	            )
                  </k>
                  <env>  i |-> I2:Int
                         s |-> S2:Int 
                         k |-> K2:Int
                  ...</env>
                </config>
                <guard> sqsum |-> true </guard>
              ...</task>)
              =>
              success
  when (I1 ==Int I2)
       andBool (S1 ==Int S2)
       andBool (K2 ==Int I2 *Int I2)

/*@
  The initial configuration:
*/

  rule [initial] :
       <T> 
         <tasks>
           .
         </tasks>
       </T>
        =>
        <T> 
         <tasks>
            <task>
               <config>
                 <k> 
		    while (i <= n) do (
		      s := s + i * i;
		        i := i + 1
		    )
                  </k>
                 <env> n |-> n0 s |-> s0 i |-> i0  </env>
               </config>
               <config>
                 <k>
		    while (i <= n) do (
		      s := s + k;
		        (k := k + i + i + 1;
		           i := i + 1)
	            )
                 </k>
                 <env> n |-> n0 s |-> s0 i |-> i0 k |-> i0 *Int i0  </env>
              </config>
              <formula> true </formula>
              <guard> sqsum |-> false </guard>
           </task>
         </tasks>
       </T>

endmodule
