/*!
\setlength{\parindent}{1em}
\title{CinK -- an experiment on how to think in \K}
\author{Dorel Lucanu (\texttt{dlucanu@info.uaic.ro}) and 
        Traian Florin \c{S}erb\u{a}nu\c{t}\u{a} (\texttt{traian.serbanuta@info.uaic.ro})}
\organization{Alexandru Ioan Cuza University of Ia\c{s}i, Romania}
\newcommand{\myparagraph}[1]{\textbf{#1}}
\newcommand{\KTool}{\K tool\xspace}
\newcommand{\Cink}{CinK\xspace}
\newcommand{\Cpp}{\mbox{C\raisebox{.2ex}{\small\!+\!+}}\xspace}
*/

/*@ \section{Introduction}

\Cink is a kernel of the \Cpp language we used to experiment with \K.
The language is used
an example for teaching classes and is refered in several research papers.

We assume the reader is already familiar with the \K Framework and the 
\KTool and here we try to share our experiece in defining a languages with some
specific features, as \Cpp is. 

\Cink is developed in several iterations, each iteration adding an incremental 
contribution.

This file includes the starting iteration, where the basic constructions of 
\Cink as arithmetic boolean expressions without side-effects, imperative 
statements, simple threads, are defined. The variables can be declared only in
the main block of the function. 


*/

/*@ \section{Syntax}
The syntax of \Cink is written using the last version at the moment of the 
\KTool. Since the language is relatively small, we use the facilities the 
\KTool offers for deffining the syntax.This is given using a BNF-like 
notation enriched with annotations and priority specifications.
In this way, the rules giving semantics are written using the \Cink 
syntax. However, in order to avoid some ambiguous parsings, some rules are
written using the corresponding \K abstract syntax trees. 
*/

module CINK-SYNTAX 

  /*@ \subsection{Declarations}
    The declarations are used for declaring variables and function names
    together with their return types.
    We consider only integer and boolean variables. A return type of a function
    could be an integer, a boolean, or \texttt{void}.
  */

  syntax Decl ::= "int"  Exps 
                | "void" Exps
                | "bool" Exps

  /*@ \subsection{Expressions} */

  /*@ The constants of the builtin types are primitive constructs and therefore
      they should be values.  
      The sort for values will be extended in the module describing the 
      semantics. 
      We prefer to declare \texttt{cin} and \texttt{cout} as values rather 
      than identifiers; the reason for this decision will be explained later.
   */

  syntax Val ::= "cout" | "cin" | Bool | String | Int

  /*@
    We included in CinK a small subset of \Cpp language, the missing operators
    can be easily added in a similar way. Recall that the most important (from
    the semantic point of view) thing we have to mention for operators is the
    attribute \texttt{strict}, that specifies the evaluation order of the 
    operands. For instance, the arithmetic binary 
    operators are strict in both arguments, hence the behavior of some 
    programs could be undefined or non-determinsitic because the evaluation
    of the arguments could have side-effects.  The assignment operator is strict
    only in the second argument because the first argument must be evaluated 
    to an l-value. These features are common to many languages. In contrast
    to the other examples, the function call expression is strict only in the
    first argument (the function name) because the evaluation of the arguments
    it is depending on the bindding mechanism of the corresponding argument: 
    this can be call-by-value or call-by-reference. These two mechansims will
    be explained later. 
   */
  syntax Exp ::= Id | Val
               | "(" Exp ")"  [bracket]
               | Exp "(" Exps ")" [strict(1)]
               > left:
                 Exp "*" Exp [strict]
               | Exp "/" Exp [strict]
               | Exp "%" Exp [strict, latex({#1}\%{#2})] 
               >  left:
                 Exp "+" Exp [strict, plus]
               | Exp "-" Exp [strict]
               > left:
                 Exp ">" Exp  [strict]
               | Exp "<=" Exp [strict, latex({#1}\leq{#2})]
               | Exp "==" Exp [strict]
               >
                 "!" Exp [strict] 
               > 
                 Exp "&&" Exp [left, strict(1), latex({#1}\mathrel{\&\&}{#2})]
               > 
                 Exp "||" Exp [left, strict(1)]
               > left:
                 Exp "<<" Exp [left, seqstrict, latex({#1}\mathrel{\tt <<}{#2})]
               | Exp ">>" Exp [left, latex({#1}\mathrel{\tt >>}{#2})]
               >
                 Exp "=" Exp [right, strict(2)]
               >
                 "endl"
  /*@
    The name of the main function is used to start the computation of a
    program and therefore it must be declared:
   */
  syntax #Id ::= "main" 

  /*@ \subsection{Statements}
    For now, we include in CinK only (a subset) of the imperative statements:
    expresion statement, bloc, sequential composition, while, and conditionals.
    We also added a minimal support for threads, similar to IMPPP, but using a
    \Cpp syntax and semantics.
   */

  syntax Stmt ::= Exp ";" [strict]
               | "#include" "<iostream>" 
                 [latex(\texttt{\#include<iostream>})]
               | "using" "namespace" "std" ";" 
                 [latex(\texttt{using namespace std;})]
               | Decl ";"
               | "{" "}"
               | "{" Stmts "}"
               | "while" "(" Exp ")" Stmt 
               | "return" Exps ";" // [strict]
               | Decl "(" Decls ")" "{" Stmts "}"
               | "if" "(" Exp ")" Stmt "else" Stmt [strict(1)]
               >
                 "if" "(" Exp ")" Stmt
               | "std::thread" Id "(" Exps ")" ";"
  /*@
    A program is a sequence of statements:
  */
  syntax Pgm ::= Stmts 

  /* \subsection{Lists} */

//  syntax Stmts ::= List{Stmt,""}
  syntax Stmts ::= Stmt | Stmts Stmts [left]

  /*@
    The above definitions are using lists of expressions and lists of 
    declarations, which are declared as follows:
  */
  syntax Exps  ::= List{Exp,  ","} [strict]
  syntax Decls ::= List{Decl, ","}

endmodule

module CINK
  imports CINK-SYNTAX

  /*@ \subsection{Values.} 
    The values are a very important syntactic category in the definition
    of any language; with them, we are able to know when the evaluation
    of an expression is finished. This piece of information is crucial, e.g.,
    for the heating and cooling rules. 
    We already defined the subset of values that is part of the syntax, 
    namely the values given by the primitive types. Here we estend the set
    o values with intermediate constructs needed to execute programs. 
    Such a value is\texttt{void}, which "paradoxally" denotes in fact 
    "no value". The lambda abstractions are used for storing the
    functions. Similar to other \K examples (IMP, IMPPP, SIMPLE), the 
    functions are stored similar to variables and therefore their definitions
    are seen as values. The values of the form \texttt{loc($L$:Int)} designate
    locations and they are used as result for the evaluation of the l-values.
    As usual, all values must be subsorted to the \texttt{KResult} sort.
   */


  syntax LVal ::= "loc" "(" Int ")"

  syntax Val ::= "void" | "undefined" | LVal
               | "lambda" "(" Decls "@" Stmts ")" 
                 [latex(\lambda\,{#1}\mathrel{\bullet}{#2})]

  syntax Vals ::= List{Val,","}
  syntax KResult ::= Val

  /*@ \subsection{Memory Locations} */

  syntax Location ::= Token{"noLocation"}

  syntax Int ::= Location


  /* \subsection{Auxiliary constructs.} */


  /*@
    \texttt{execute} is used to start the computation of a program; and
    \texttt{noname} for the initial name of a thread.
  */
  syntax K ::= "execute" | "noname"

 /*@
   The next two constructors are used for storing the enavironment and the
   rest of the computation in the call stack (\texttt{fstack}). 
 */
  syntax ListItem ::= "(" List "," K ")"
                    | "[" Map "]"

 /*@ \subsection{Configuration.} 
   The configuration is standard for such languages (compare it to that of IMPP
   and SIMPLE).
   The threads are included in a cell named \texttt{threads}, where each cell
   \texttt{thread}, representing the current of a thread, includes a cell 
   \texttt{k} for the local computations, a cell \texttt{env} for the local
   environment, and a cell \texttt{fstack} for
   the managing the local configurations when a function call expression 
   or a return statement is executed.
  */

  configuration <T color="yellow">
                  <threads color="pink">
                    <thread multiplicity="*" color="purple"> 
                      <name color="yellow"> noname </name>
                      <k color="green"> ($PGM:Pgm ~> execute) </k>
                      <env color="LightSkyBlue"> .Map </env>
                      <fstack color="orange"> .List </fstack>
                    </thread>
                  </threads>
                  <br/>
                  <genv color="SkyBlue"> .Map </genv>
                  <store color="white"> .Map </store>
                  <in color="magenta" stream="stdin"> .List </in>
//                  <out color="Orchid"> .List </out>
                  <out color="Orchid" stream="stdout"> .List </out>
//                  <nextLoc> 0 </nextLoc>
                </T>

  /*@
    In order to have a minimal set of rules, some syntactic constructs
    are desugared. The desugaring can be done using the structural rules.
    In order to avoid some ambiguous parsings, some terms are written using
    the \K AST notation.
   */

  /*@ The desugaring rule for the if-then statement: */
  rule if(B:Exp) St:Stmt => if(B) St else {}  [macro]
  
  /*@
    The desugaring rule for statements declaring multiple variables.
*/
/*
 Here
    the use of the \K AST notation allows to write a single rule for all
    declaration types. The function \texttt{isDeclLabel}$(KL)$ returns 
    true only if $KL$ is a label of a declaration; it is defined later,
    in the subsection devoted to the auxiliary functions.
   */
/*
  rule '_;(KL:KLabel('_`,_(E:Exp,, Es:Exps)))
       =>
       '__('_;(KL('_`,_(E,, .Exps))),, '_;(KL(Es)))
       when isDeclLabel(KL)
       andBool (Es =/=K .Exps)
       [macro]
*/
   rule int E:Exp, Es:Exp ; => int E; int Es; [macro]
   rule bool E:Exp, Es:Exp ; => int E; int Es; [macro]
   rule void E:Exp, Es:Exp ; => int E; int Es; [macro]

  /*@
    Desugaring rule for variable declarations with initialization.
    The previous desugaring rule allows us
    to consider here only simple variable declarations, which are not 
    aliases. 
   */

/*
  rule '_;(KL:KLabel('_`,_('_=_(E1:Exp,, E2:Exp),, .Exps)))
       =>
       '__('_;(KL('_`,_(E1,, .Exps))),, '_;('_=_(getName(E1),, E2)))
       when isDeclLabel(KL)
       [macro]
*/

   rule int E1:Exp = E2:Exp ; => int E1; E1 = E2; [macro]
   rule bool E1:Exp = E2:Exp ; => bool E1; E1 = E2; [macro]



  /*@ \subsection{Declarations.} */

  /*@
    Function declaration: a function is a stored similar to a variable,
    where the value stored in the associated location is the lambda
    abstraction of the function. 
   */


  rule <k>  (Decl:Decl (Xl:Decls) {Sts:Stmts})::Stmt  => .  ...</k> 
       <env>... . =>  (getName(Decl) |-> L) ...</env>
       <store>... . => (L |-> lambda(Xl @ Sts)) ...</store>
when fresh(L:Location)
//       <nextLoc> L:Int => (L +Int 1) </nextLoc>
       [fun-decl, structural]

/*
  rule <k> '_`(_`)`{_`}(Decl:Decl,, Xl:Decls,, Sts:Stmts) => .  ...</k> 
       <env>... . =>  (getName(Decl) |-> L) ...</env>
       <store>... . => (L |-> lambda(Xl @ Sts)) ...</store>
       <nextLoc> L:Int => (L +Int 1) </nextLoc>
       [fun-decl, structural]
*/

  /*@
    The rules for variable declarations:
   */

  rule [var-decl] :
       <k> int X:Id => void  ...</k>      
       <env> Env:Map => Env[L/X] </env>
       <store>... . => (L |-> undefined) ...</store>
 when fresh(L:Location)
//      <nextLoc> L:Int => (L +Int 1) </nextLoc>
       [structural]

  rule [var-decl] :
       <k> bool X:Id => void  ...</k>      
       <env> Env:Map => Env[L/X] </env>
       <store>... . => (L |-> undefined) ...</store>
when fresh(L:Location)
//       <nextLoc> L:Int => (L +Int 1) </nextLoc>
       [structural]

/*
  rule [var-decl] :
       <k> KL:KLabel('_`,_(E:Exp,, .Exps)) => void  ...</k>      
       <env> Env:Map => Env[L/getName(E)] </env>
       <store>... . => (L |-> undefined) ...</store>
       <nextLoc> L:Int => (L +Int 1) </nextLoc>
       when isDeclLabel(KL)
       [structural]
*/
  /*@ The following two constructs have no semantics yet; they are used now only 
      for having a full compatibility with \Cpp, e.g., the \Cink programs can be 
      compiled with a \Cpp compiler. */
  rule <k> #include <iostream> => .  ...</k>
       [include, structural]

  rule <k> using namespace std;=> .  ...</k>
       [using, structural]

  /*@ 
    The auxiliary construct \texttt{execute} is used to initialize the 
    execution of a program, which for the case of \Cink consists of the call
    of the main function.
  */

  rule <k> execute => main(.Vals); </k>
       <env> Env:Map </env>
       <genv> . => Env:Map </genv>
       [main, structural]
  
  /*@ \subsection{Expressions Evaluation.} */

  /*@
   The following expressions are strict. 
  */
  rule I1:Int + I2:Int => I1 +Int I2 [plus,structural]

  rule I1:Int - I2:Int => I1 -Int I2 [structural]

  rule I1:Int * I2:Int => I1 *Int I2 [structural]

  rule I1:Int / I2:Int => I1 /Int I2 when I2 =/=Int 0 [structural]
 
  rule I1:Int % I2:Int => I1 %Int I2 when I2 =/=Int 0 [structural]

  rule I1:Int > I2:Int => (I1 >Int I2) [structural]

  rule I1:Int <= I2:Int => (I1 <=Int I2) [structural]

  rule I1:Int == I2:Int => (I1 ==Int I2) [structural]
 
  /*@
   Here are the rules for the expressions having the strict attribute 
   declared in the syntax.
  */

  rule true && B:Exp => B [structural]
  rule false && B:Exp => false [structural]
  rule true || B:Exp => true [structural]
  rule false || B:Exp => B [structural]
  rule ! false  => true [structural]
  rule ! true => false [structural]

  rule endl => "\n" [structural]


  /*@ \subsection{Memmory operations.} */


  /*@
    The evaluation of a variable name as an r-value:
  */
  rule <k> X:Id => V ...</k>
       <env>... X |-> L:Int ...</env>
       <store>... L |-> V:Val ...</store>
       [kripke(mem-lookup)]

  /*@
    The memory update is given by the assignment operator. The left-hand side
    must be evaluated to an l-value and the right-hand side to an r-value.
   */
  rule <k> X:Id = V:Val => V  ...</k>
       <env>... X |-> L:Int ...</env>
       <store>... L |-> (_ => V) ...</store>
       [kripke(mem-update)]

  /* \subsection{Control Statements.} */

  /*@
    As usual, the \texttt{while} statement is desugared using the 
    \texttt{if-then-else} statement.
  */
  rule while(B:Exp) St:Stmt => if (B) {St while(B) St} else {}
       [while, structural]

  /*@
    Since \texttt{if} is strict in the first argument, which is a boolean
    expression, proceed by case-analysis on the result values:
  */
  rule if(false) _ else St:Stmt => St [if-false]
  rule if(true) St:Stmt else _ => St [if-true]


  /*@
    The semantics of the expression statement consists of removing the
    value obtained by evaluating the expression. Recall that the statement
    is strict.
   */
  rule <k> (V:Val; ~> K:K) => K </k> 
       when K =/=K .K
       [instr-expr]
  /*@
    Block:\\
      -- the case of non-empty block
  */
  rule { Sts:Stmts } => Sts
       [block, structural]

  /*@ -- the case of the empty block: */
  rule {} => .  [block-empty, structural]

  //@ The sequential composition is just a sequence of computations:
  rule (Sts:Stmts Sts':Stmts) => (Sts ~> Sts')
       [seq-comp, structural] 

  /*@ \subsection{Input/Output Statements.} */

  /*@ Writting in the the standard stream \texttt{cout}: */
  rule <k> cout << V:Val => cout  ...</k>  
       <out>... . => (ListItem(V) ListItem(" ")) </out>
       [print-stream, print]

  /*@
   In order to read from the standard stream \texttt{cin}, the expression
   from the right-hand side must be evaluated to an l-value:
  */
  rule <k> cin >> X:Id => cin  ...</k>
       <env>...  X |-> L:Int  ...</env>
       <store>... L |-> (_ => I)  ...</store>
       <in> (ListItem(I:Int) => .)  ...</in>
       [read-stream]

  /*@
    \subsection{The function call expression}
    The function name is evaluated to its value, which is a lambda 
    abstraction: $\it Xl$ is the list of parameters, $\it Sts$ is body of
    the function. The {\sc function-call} rule pushes the calling context,
    i.e., the remainder of the computation $K$ and environment stack 
    (including the current environment) on top of the function stack, 
    while the {\sc return} rule uses the information there to restore 
    the environment and computation of the caller.
    Since the evaluation strategy for the second argument is depending on
    the binding specification in the function signature, the function call
    expression is declared strict only in its first argument.
   */

  /*@
    The rule defining the evaluation of a function call expression evaluates
    first the actual parameters, and then binds the 
    values to the formal parameters and executes the body, while saving the
    calling context in case of an abrupt return. This is done by mimic the
    heating-cooling mechanism (the first rule is a heating-like one, and the
    second a cooling-like one).
   */

  rule <k> lambda(Xl:Decls @ Sts:Stmts)(Vl:Exps)
           =>
           evaluate Vl to .Vals following Xl; ~> lambda(Xl:Decls @ Sts:Stmts)(HOLE)
       ...</k> 

/*
  rule <k> ('_`(_`)(lambda(Xl:Decls @ Sts:Stmts),, Vl:Exps))
           =>
           evaluate Vl to .Vals following Xl; ~> '_`(_`)(lambda(Xl:Decls @ Sts:Stmts),, HOLE)
       ...</k> 
*/
  rule <k> (Vl:Vals ~> lambda(Xl:Decls @ Sts:Stmts)(HOLE) ~> K:K)
           => 
           (bind Vl to Xl; ~> Sts ~> return void;)
       </k>
       <br/>
       <genv> GEnv:Map </genv>
       <env> Env:Map => GEnv </env>
       <fstack> . => ([Env], K) ...</fstack>
       [fun-call]

/*
  rule <k> (Vl:Vals ~> '_`(_`)(lambda(Xl:Decls @ Sts:Stmts),, HOLE) ~> K:K)
           => 
           (bind Vl to Xl; ~> Sts ~> return void;)
       </k>
       <br/>
       <genv> GEnv:Map </genv>
       <env> Env:Map => GEnv </env>
       <fstack> . => ([Env], K) ...</fstack>
       [fun-call]
*/

  /*@
    To evaluate actual parameters according to their declared strategy we will
    make use of the power of \K evaluation contexts. 
    The actual parameters must be evaluated using 
    the $\terminalNoSpace{evaluate}$ construct and $\terminalNoSpace{following}$ 
    the list of formal parameters.
  */

  syntax Exps ::= "evaluate" Exps "to" Vals "following" Decls ";"

  /*@
    For a formal parameter declared with the call-by-value mechanism,
    the corresponding argument expression must be evaluated to an rvalue as
    specified by by the following contextual declaration:
  */

  context evaluate (HOLE, _:Exps) to _:Vals following (int X:Id, _:Decls);


  /*@
    \noindent This second context uses again the special type of context used
    above for $\terminalNoSpace{evaluate}$, by requesting that the expression
    on position $\khole{}$ be evaluated as an lvalue.
    \par
    The following two rules, together with the strict evaluation strategy for
    lists of expressions complete the semantics of $\terminalNoSpace{evaluate}$
    by recursing into the lists:
  */

  rule evaluate(V:Val, El:Exps => El) to (Vl:Vals => V,Vl)
         following (Dec:Decl, Xl:Decls => Xl);
       [structural]
   
  rule evaluate .Exps to Vl:Vals following .Decls; => Vl [structural]

   /*@
     \subsubsection{Binding mechanisms}
     Similarly to the evaluation rules, the binding rules are also different 
     for the two parameter passing styles.
     As we have already seen, the binding is performed using an auxiliary 
     construction:
   */

  syntax K ::= "bind" Vals "to" Decls ";"  

  /*@
  For call-by-value, the passed value $V$ is stored into a new memory location
  which is bound to the formal parameter:
  */
  rule <k> bind((V:Val, Vs:Vals) => Vs)
           to((int X:Id, Xl:Decls) => Xl); 
       ...</k>
       <env> Env:Map => Env[L/X] </env>
       <store>... . => L |-> V ...</store>
when fresh(L:Location)
//       <nextLoc> L:Int => L +Int 1 </nextLoc>
       [structural]

  /*@
    Finally, once all parameters have been bound, the binding construct 
    dissolves:
   */
  rule bind .Vals to .Decls; => . [ structural ]

  /*@
    \subsection{Function Return.}
    Similar to \Cpp, the argument of a return statement is a list of
    expressions (note that Cink does not have yet the comma operator). 
  */

  //@ The case when the argument is the empty list:
  rule return .Exps ; => return void; 

  /*@
    Similar to the comma operator, the evaluation of the return argument
    is given from left to right. Since the expression lists are strict,
    if we declare the return statement strict then the evaluation is given
    from right to left (in the oposite order). Therefore we use a context
    declaration to have the right evaluation order:
  */
  context return HOLE, Es:Exps ;

  /*@
    We may write now the rules for the case when the first element of the
    list is evaluated. The first rules treats the case when theare are 
    elements to be evaluated, and the second one the case whne the evaluation
    is finished.
  */
  rule return V:Val, Es:Exps ; => return Es ; 
       when Es =/=K .Exps 
       [return]

  rule <k> (return V:Val; ~> _) => (V ~> K) </k>
       <env> _ => Env </env>
       <fstack> ([Env:Map], K:K) => . ...</fstack>
       [return]

  /*@
    \subsection{Threads.}
    For now, \Cink includes a minimal support for threads, namely the creation 
    of a thread and the ending of a thread. The statement for creating a thread
    specifies the name of the thread \textit{T}, the name of a function
    \textit{F}, and the arguments \textit{El} of the function.
    The rule giving semantics to this statement, creates a new cell 
    \texttt{thread}, where the computation from the cell \texttt{k} of the new
    thread is the function call expression given as arguments, and the
    environment of the new thread is current environment of the current
    thread.
  */

  rule <thread>...
         <k> std::thread T:Id(F:Id, El:Exps); => . ...</k>
         <env> Env:Map </env>
       ...</thread>
       (. => 
        <thread>... 
          <name> T </name>  
          <k> F(El); </k>
          <env> Env </env>  
        ...</thread>
       )
       [thread]

  /*@
    A thread is finished (and deleted) when the content of its \texttt{k}
    cell is empty:
  */
  rule <thread>... <k>.K</k>  ...</thread> => . [thread-end]

  /*@
    \subsection{Auxiliary Functions and Rules.}
    Here we winclude the semantics for the auxiliary constructs, used to give
    semnatics for \Cink.
  */
  /*
   The function \texttt{isDeclLabel} tests whether a \K label is a declaration.
   It allows to treat the declaration in a compact way.
  */
/*
  syntax Bool ::= "isDeclLabel" "(" KLabel ")" [function]

  rule isDeclLabel(KL:KLabel) => true
       when       KL ==KLabel 'int_
       orElseBool KL ==KLabel 'bool_ 
       orElseBool KL ==KLabel 'void_
*/

  /*@
    The next operator returns the variable name from an expression occurring
    in a declaration:
  */
  syntax  Id ::= "getName" "(" K ")" [function]

  rule getName(X:Id) => X
  rule getName(int E:Exp) => getName(E)
  rule getName(bool E:Exp) => getName(E)
  rule getName(void E:Exp) => getName(E)
  rule getName(E1:Exp = E2:Exp) => getName(E1)

endmodule




