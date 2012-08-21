/*!
\setlength{\parindent}{1em}
\title{CinK -- an experiment on how to think in \K}
\author{Dorel Lucanu (\texttt{dlucanu@info.uaic.ro}) and 
        Traian Florin \c{S}erb\u{a}nu\c{t}\u{a} (\texttt{tserban2@illinois.edu})}
\organization{Alexandru Ioan Cuza University of Ia\c{s}i, Romania}
\newcommand{\myparagraph}[1]{\textbf{#1}}
\newcommand{\KTool}{\K tool\xspace}
\newcommand{\Cink}{CinK\xspace}
\newcommand{\Cpp}{\mbox{C\raisebox{.2ex}{\small\!+\!+}}\xspace}
*/

/*@ \section{Introduction}

CinK is a kernel of the \Cpp language we used to experiment with \K.
The language is used
an example for teaching classes and is refered in several research paper.

In this report we briefly present the \K definition of CinK. The most part of
the text is automatically generated with the \K tool, therefore there are some
differences btween the source code and the pdf version. For instance, the
terminal syntax declarations are enclosed into quotes but in the pdf version
these are not displayed. In pdf version, for ease reading reasons, there are 
used different fonts in order to distinguish between different syntactic 
categories.

The report is not intended to be an introduction to \K. 
We assume the reader is already familiar with the \K Framework and the 
\KTool and here we try to share our experiece in defining a languages with some
specific features, as \Cpp is. Such features includes a clear distinction
between l-values and r-values, declaration of aliases, and 
various parameters passing mechanisms.
We also extend the definition with a small property language, including LTL
formulas, and we show how the \KTool is used together with Maude system 
for analazing \Cink programs.

The \K definition of \Cink is continuously evolving, so this report presents
the status of this definition at the publication date. 

%We refer the reader to~\cite{k-primer-2012-v25} for a brief presentation of 
%the \KTool.
*/

/*@ \section{Syntax}
The syntax of \Cink is written using the last version at the moment of the 
\KTool. Since the language is relatively small, we use the facilties the 
\KTool offers for deffining the syntax.This is given using a BNF-like 
notation enriched with annotations and priority specifications.
In this way, the rules giving semantics are written using the \Cink 
syntax. However, in order to avoid some ambiguous parsings, some rules are
written using the corresponding \K abstract syntax trees. 
*/

module CINK-LANG-SYNTAX 

  imports BUILTIN-SYNTAX-HOOKS

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
    of the arguments could have side-effects. Initially, their strictness was
    declared directly in the syntax, uing the attribute strict. When we gave 
    semantics to the prefix increment operator, we realized that this is not
    a good choice. Since some operators, like the prefix increment, return
    l-values, in Cink the l-values and r-values can mixtly occur in the 
    evaluation of an expression. We will discuss in detail this apect when
    we give semantics to the operators.  The assignment operator is strict
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
               | Id "(" Exps ")" [strict(1)]
               | "&" Exp
               | "*" Exp [strict]
               | "++" Exp
               > left:
                 Exp "*" Exp 
               | Exp "/" Exp 
               | Exp "%" Exp [latex("{#1}\%{#2}")] 
               >  left:
                 Exp "+" Exp 
               | Exp "-" Exp 
               > left:
                 Exp ">" Exp 
               | Exp "<=" Exp [latex("{#1}\leq{#2}")]
               | Exp "==" Exp 
               >
                 "!" Exp [strict] 
               > 
                 Exp "&&" Exp [left, strict(1), latex("{#1}\mathrel{\&\&}{#2}")]
               > 
                 Exp "||" Exp [left, strict(1)]
               > left:
                 Exp "<<" Exp [left, seqstrict, latex("{#1}\mathrel{\tt <<}{#2}")]
               | Exp ">>" Exp [left, latex("{#1}\mathrel{\tt >>}{#2}")]
               >
                 Exp "=" Exp [right]
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
                 [latex("\texttt{\#include<iostream>}")]
               | "using" "namespace" "std" ";" 
                 [latex("\texttt{using namespace std;}")]
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
    The above definitions are using list of expressions and lists of 
    declarations, which are declared as follows:
  */
  syntax Exps  ::= List{Exp,  ","} [strict]
  syntax Decls ::= List{Decl, ","}

endmodule

module CINK-LANG-SEMANTICS
  imports CINK-LANG-SYNTAX

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
                 [latex("\lambda\,{#1}\mathrel{\bullet}{#2}")]

  syntax Vals ::= List{Val,","}
  syntax KResult ::= Val

  /* \subsection{Auxiliary constructs.} */

  /*@
    In Cink, the expressions can be evaluated to l-values or to r-values,
    depending on the context they are used.
    Historically, the names of these two categories are coming from the fact 
    that an lvalue expression can be used in the left hand side of an 
    assignment and an rvalue expression can be used in the right hand side of 
    an assignment.
    Semantically, an l-value expression is evaluated to a location and an 
    r-value expression is evaluated to a value that can be stored into a
    location.
    As we mentioned earlier, we use the sort \texttt{LVal} for l-values.
    We also use two auxiliary semantics constructs that help to specify
    the places where an l-value (resp. r-value) is expected. 
  */
  syntax Exp ::=  "lvalue" "(" Exp ")" | "rvalue" "(" Exp ")" [strict]

  /*@
    We also use some  other special symbols:
    \texttt{execute} is used to start the computation of a program; and
    \texttt{noname} for the initial name of a thread.
  */
  syntax K ::= "execute" | "noname"

 /*@
   The next two constructors are used for storing the enavironment and the
   rest of the computation in the call stack (\texttt{fstack}) and in the block 
   stack (\texttt{bstack}). 
 */
  syntax ListItem ::= "(" List "," K ")"
                    | "[" Map "]"

 /*@ \subsection{Configuration.} 
   The configuration is standard for such languages (compare it to that of IMPP
   and SIMPLE).
   The threads are included in a cell named \texttt{threads}, where each cell
   \texttt{thread}, representing the current of a thread, includes a cell 
   \texttt{k} for the local computations, a cell \texttt{env} for the local
   environment, a cell \texttt{bstack} for managing the environments
   when the execution enters or exits a block, and a cell \texttt{fstack} for
   the managing the local configurations when a function call expression 
   or a return statement is executed.
   The cell \texttt{bstack} is specific to this definition, it does not appear
   in the definition of the other similar languages.
  */

  configuration <T color="yellow">
                  <threads color="pink">
                    <thread multiplicity="*" color="purple"> 
                      <name color="yellow"> noname </name>
                      <k color="green"> ($PGM:Pgm ~> execute) </k>
                      <env color="LightSkyBlue"> .Map </env>
                      <bstack color="orange"> .List </bstack>
                      <fstack color="orange"> .List </fstack>
                    </thread>
                  </threads>
                  <genv color="SkyBlue"> .Map </genv>
                  <store color="white"> .Map </store>
//                  <br/>
                  <in color="magenta" stream="stdin"> $IN:List </in>
//                  <out color="Orchid"> .List </out>
                  <out color="Orchid" stream="stdout"> .List </out>
                  <nextLoc> 0 </nextLoc>
                </T>

  /*@
    In order to have a minimal set of rules, some syntactic constructs
    are desugared. The desugaring can be done using the structural rules.
    In order to avoid some ambiguous parsings, some terms are written using
    the \K AST notation.
   */

  /*@ The desugaring rule for the if-then statement: */
  rule if(B:Exp) St:Stmt => if(B) St else {}  [anywhere]
  
  /*@
    The desugaring rule for statements declaring multiple variables. Here
    the use of the \K AST notation allows to write a single rule for all
    declaration types. The function \texttt{isDeclLabel}$(KL)$ returns 
    true only if $KL$ is a label of a declaration; it is defined later,
    in the subsection devoted to the auxiliary functions.
   */
  rule '_;(KL:KLabel('_`,_(E:Exp,, Es:Exps)))
       =>
       '__('_;(KL('_`,_(E,, .Exps))),, '_;(KL(Es)))
       when isDeclLabel(KL)
       andBool (Es =/=K .Exps)
       [anywhere]


  /*@
    Desugaring rule for variable declarations with initialization:
     e.g., \texttt{int *y = \&x;} is desugared into 
    \texttt{ int *y; y = \&x;}. The previous desugaring rule allows us
    to consider here only simple variable declarations, which are not 
    aliases. 
   */
  rule '_;(KL:KLabel('_`,_('_=_(E1:Exp,, E2:Exp),, .Exps)))
       =>
       '__('_;(KL('_`,_(E1,, .Exps))),, '_;('_=_(getName(E1),, E2)))
       when isDeclLabel(KL) 
       andBool (isAlias('_=_(E1,, E2)) =/=K true)
       [anywhere]


  /*@ \subsection{Declarations.} */

  /*@
    Function declaration: a function is a stored similar to a variable,
    where the value stored in the associated location is the lambda
    abstraction of the function. 
   */
  rule [fun-decl] :
       <k> '_`(_`)`{_`}(Decl:Decl,, Xl:Decls,, Sts:Stmts) => .  ...</k> 
       <env>... . =>  (getName(Decl) |-> L) ...</env>
       <store>... . => (L |-> lambda(Xl @ Sts)) ...</store>
       <nextLoc> L:Int => (L +Int 1) </nextLoc>
       [structural]

  /*@
    The rules for variable declarations.\\
    -- declaration of an alias: 
  */

  context KL:KLabel('_`,_(&_ = (HOLE => lvalue(HOLE)),, .Exps))
       when isDeclLabel(KL)

  /* */
  rule [alias-decl] :
       <k> KL:KLabel('_`,_(& X:Id = loc(L:Int),, .Exps)) => void  ...</k>      
       <env> Env:Map => Env[L/X] </env>
       when isDeclLabel(KL)
       [structural]

  /*@ -- declaration of a variable: */
  rule [var-decl] :
       <k> KL:KLabel('_`,_(E:Exp,, .Exps)) => void  ...</k>      
       <env> Env:Map => Env[L/getName(E)] </env>
       <store>... . => (L |-> undefined) ...</store>
       <nextLoc> L:Int => (L +Int 1) </nextLoc>
       when isDeclLabel(KL)
       andBool (isAlias(E) =/=K true)
       [structural]

  /*@ The following two constructs have no semantics yet; they are used now only 
      for having a full compatibility with \Cpp, e.g., the \Cink programs can be 
      compiled with a \Cpp compiler. */
  rule [include] :
       <k> #include <iostream> => .  ...</k>
       [structural]

  rule [using] :
       <k> using namespace std;=> .  ...</k>
       [structural]

  /*@ 
    The auxiliary construct \texttt{execute} is used to initialize the 
    execution of a program, which for the case of \Cink consists of the call
    of the main function.
  */

  rule <k> execute => '_;('_`(_`)(main,, .Vals)) </k>
       <env> Env:Map </env>
       <genv> . => Env:Map </genv>
       [structural]
  
  /*@ \subsection{Expressions Evaluation.} */

  /*@
   The following expressions are strict, but their strictness is declared using
   contextual declarations in order to be able to specify whether an argument
   is an l-value or an r-value. 
  */
  context (HOLE => rvalue(HOLE)) + _
  context _ + (HOLE => rvalue(HOLE))
  rule I1:Int + I2:Int => I1 +Int I2 [structural]

  context (HOLE => rvalue(HOLE)) - _
  context _ - (HOLE => rvalue(HOLE))
  rule I1:Int - I2:Int => I1 -Int I2 [structural]

  context (HOLE => rvalue(HOLE)) * _
  context _ * (HOLE => rvalue(HOLE))
  rule '_*_(I1:Int,, I2:Int) => I1 *Int I2 [structural]
//  rule I1:Int * I2:Int => I1 *Int I2 [structural]

  context (HOLE => rvalue(HOLE)) / _
  context _ / (HOLE => rvalue(HOLE))
  rule I1:Int / I2:Int => I1 /Int I2 when I2 =/=Int 0 [structural]
 
  context (HOLE => rvalue(HOLE)) % _
  context _ % (HOLE => rvalue(HOLE))
  rule I1:Int % I2:Int => I1 %Int I2 when I2 =/=Int 0 [structural]

  context (HOLE => rvalue(HOLE)) > _
  context _ > (HOLE => rvalue(HOLE))
  rule I1:Int > I2:Int => (I1 >Int I2) [structural]

  context (HOLE => rvalue(HOLE)) <= _
  context _ <= (HOLE => rvalue(HOLE))
  rule I1:Int <= I2:Int => (I1 <=Int I2) [structural]

  context (HOLE => rvalue(HOLE)) == _
  context _ == (HOLE => rvalue(HOLE))
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

  rule [indirection] :
       <k> (* L:Int) => V ...</k>
       <store>... L |-> V ...</store>

  /*@ The dereferencing operator: */
  context & (HOLE => lvalue(HOLE))
  rule & loc(L:Int) => L


  /*@ \subsubsection{The prefix increment operator}
    Here is the description of this operator from the manual of \Cpp 2011:
    "The operand of prefix ++ is modified by adding 1, or set to true 
    if it is bool (this use is deprecated). The operand shall be a 
    modifiable lvalue. The type of the operand shall be an arithmetic 
    type or a pointer to a completely-defined object type. 
    The result is the updated operand; it is an lvalue, and it is a 
    bit-field if the operand is a bit-field."\\
    This definition raises some problems.
    We suppose that we want to evaluate the
    expression \texttt{y + (++x)}; since the addition operator is strict in 
    both arguments, it will be reduced something like $\it I + loc(L)$ and 
    in that case $\it loc(L)$ should be evaluate at the value stored into
    the location $L$. On the other hands, the evaluation of the expression
    \texttt{++ (++x)} uses the l-value returned by the operator.
    This is one reason for that we make a clear distinction
    between r-value and l-value expressions and use the contexts declarations
    in order to specify how to valuate subexpressions.
  */

  context ++ (HOLE => lvalue(HOLE))
  rule <k> ++ loc(L) => loc(L) ...</k>
       <store>... L |-> (V:Int => V +Int 1) ...</store>

  /*@
    The \texttt{lvalue()} operator: if the argument is not already an l-value,
    then it is firstly evaluated. The result of the argument evaluation is an
    \texttt{Int} or an l-value (when the argument was evaluated as an l-value).
   */
  context lvalue(HOLE) 
          when isLValue(HOLE) =/=K true  

  rule lvalue(L:Int) => loc(L) [structural]

  rule lvalue(loc(L:Int)) => loc(L) [structural]


  /*@
    The \texttt{rvalue()} operator:\\
    -- the case we have got an l-value where an r-value is expected: 
  */ 
  rule <k> rvalue(loc(L:Int)) => V ...</k>
       <store>... L |-> V:Val ...</store>

  /*@
    -- the case when we got an expected r-value:
  */
  rule rvalue(V:Val) => V when isLVal(V) =/=K true


  /*@ \subsection{Memmory operations.} */

  /*@
    The evaluation of a variable name as an l-value. We distinguish two cases:\\
    -- the location is directly disignated by the variable name
  */

  rule [mem-lookup-lvalue] :
       <k> lvalue(X:Id) => loc(L) ...</k>
       <env>... X |-> L:Int ...</env>
       [transition]

  /*@
    -- the location is indirectly disignated by the variable name
  */
  rule [mem-lookup-lvalue-indirect] :
       <k> lvalue(* X:Id) => loc(V) ...</k>
       <env>... X |-> L:Int ...</env>
       <store>... L |-> V:Val ...</store>
       [transition]

  /*@
    The evaluation of a variable name as an r-value:
  */
  rule [mem-lookup-rvalue] :
       <k> X:Id => V ...</k>
       <env>... X |-> L:Int ...</env>
       <store>... L |-> V:Val ...</store>
       [transition]

  /*@
    The memory update is given by the assignment operator. The left-hand side
    must be evaluated to an l-value and the right-hand side to an r-value.
   */
  context (HOLE => lvalue(HOLE)) = _
  context _=(HOLE => rvalue(HOLE))
  rule [mem-update] :
       <k> loc(L:Int) = V:Val => V  ...</k>
       <store>... L |-> (_ => V) ...</store>
       [transition]

  /* \subsection{Control Statements.} */

  /*@
    As usual, the \texttt{while} statement is desugared using the 
    \texttt{if-then-else} statement.
  */
  rule [while] :
       while(B:Exp) St:Stmt => if (B) {St while(B) St} else {}
       [structural]

  /*@
    Since \texttt{if} is strict in the first argument, which is a boolean
    expression, proceed by case-analysis on the result values:
  */
  rule [if-false] : if(false) _ else St:Stmt => St
  rule [if-true] : if(true) St:Stmt else _ => St


  /*@
    The semantics of the expression statement consists of removing the
    value obtained by evaluating the expression. Recall that the statement
    is strict.
   */
  rule [instr-expr] : 
       <k> (V:Val; ~> K:K) => K </k> 
       when K =/=K .K
  /*@
    Since in \Cink we may have variable declarations inside of blocks, 
    each time the execution enters a block, the environment is saved in 
    the cell \texttt{bstack}.
    We define the semantics of the block statement such that the environment
    is saved only if it differs from the one stored in the top of the cell.\\
    -- the case cell \texttt{bstack} is empty:
  */
  rule [block] : 
       <k>{Sts:Stmts} => (Sts ~> popb)  ...</k>
       <env> Env:Map </env>
       <bstack> . => [Env] </bstack>
       [structural]

  /*@
    -- the case when the cell \texttt{bstack} is not empty and the current 
    environment is different from that on the top:
  */
  rule [block] : 
       <k>{Sts:Stmts} => (Sts ~> popb)  ...</k>
       <env> Env:Map </env>
       <bstack> (. => [Env]) [Env1:Map] ...</bstack>
       when Env =/=Map Env1
       [structural]

  /*@
    -- the case when the cell \texttt{bstack} is not empty and the current 
    environment is equal to that on the top:
  */
  rule [block] : 
       <k>{Sts:Stmts} => Sts  ...</k>
       <env> Env:Map </env>
       <bstack> [Env1:Map] ...</bstack>
       when Env ==Map Env1
       [structural]

  /*@ -- the case of the empty block: */
  rule [block-empty] : {} => .  [structural]

  //@ The sequential composition is just a sequence of computations:
  rule [seq-comp] : 
       (Sts:Stmts Sts':Stmts) => (Sts ~> Sts')
       [structural] 

  /*@ \subsection{Input/Output Statements.} */

  /*@ Writting in the the standard stream \texttt{cout}: */
  rule [print-stream]:
       <k> cout << V:Val => cout  ...</k>  
       <out>... . => (ListItem(V) ListItem(" ")) </out>

  /*@
   In order to read from the standard stream \texttt{cin}, the expression
   from the right-hand side must be evaluated to an l-value:
  */
  context HOLE >> _
  context _ >> (HOLE => lvalue(HOLE))
  rule [read-stream]:
       <k> cin >> loc(L) => cin  ...</k>
//       <env>...  X |-> L:Int  ...</env>
       <store>... L |-> (_ => I)  ...</store>
       <in> (ListItem(I:Int) => .)  ...</in>

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
    The rule defining the evaluation of a function call expression assumes
    that the actual parameters have already been evaluated, and binds the 
    values to the formal parameters and executes the body, while saving the
    calling context in case of an abrupt return.
   */
  rule [fun-call] : 
       <k> ('_`(_`)(lambda(Xl:Decls @ Sts:Stmts),, Vl:Vals) ~> K:K)
           =>
           (bind Vl to Xl; ~> Sts ~> return void;)
       </k> 
//       <br/>
       <genv> GEnv:Map </genv>
       <env> Env:Map => GEnv </env>
       <bstack> Stack:List </bstack>
       <fstack> . => ([Env] Stack, K) ...</fstack>
//       [large]

  /*@
    To evaluate actual parameters according to their declared strategy we will
    make use of the power of \K evaluation contexts.  First, a context 
    declaration for the function call specifies that the arguments need to be
    evaluated taking into consideration their declared strategy:
  */

  context '_`(_`)(lambda(Xl:Decls @ Sts:Stmts),, 
                 (HOLE => evaluate HOLE following Xl;))
  /*@
   This context says not only that the actual parameters must be evaluated when
   passed to a function value, but also that they need to be evaluated using 
   the $\terminalNoSpace{evaluate}$ construct and $\terminalNoSpace{following}$ 
   the list of formal parameters.
  */

  syntax Exps ::= "evaluate" Exps "following" Decls ";"

  /*@
    For a formal parameter declared with the call-by-value mechanism,
    the corresponding argument expression must be evaluated to an rvalue as
    specified by by the following contextual declaration:
  */

  context evaluate (HOLE, _:Exps) following (int X:Id, _:Decls);

  /*@ 
    For a formal parameter declared with call-by-reference mechanism,
    the corresponding argument expression must be evaluated to an lvalue:
  */

  context evaluate((HOLE => lvalue(HOLE)), _:Exps)
          following  (int & X:Id, _:Decls);

  /*@
    \noindent This second context uses again the special type of context used
    above for $\terminalNoSpace{evaluate}$, by requesting that the expression
    on position $\khole{}$ be evaluated as an lvalue.
    \par
    The following two rules, together with the strict evaluation strategy for
    lists of expressions complete the semantics of $\terminalNoSpace{evaluate}$
    by recursing into the lists:
  */

  rule evaluate(V:Val, El:Exps) following (Dec:Decl, Xl:Decls);
    => V, evaluate El following Xl;
  rule evaluate .Exps following .Decls; => .Vals

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
       <nextLoc> L:Int => L +Int 1 </nextLoc>

  /*@ For call-by-reference, the location pointed to by the lvalue is directly
      bound to the formal parameter:
  */
  rule <k> bind((loc(L:Int), Vs:Vals) => Vs)
           to((int & X:Id, Xl:Decls) => Xl); 
       ...</k>
       <env> Env:Map => Env[L/X] </env> 

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
  rule [return] : return .Exps ; => return void; [transition]

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
  rule [return] : return V:Val, Es:Exps ; => return Es ; 
       when Es =/=K .Exps 
       [transition]

  rule [return] :
       <k> (return V:Val; ~> _) => (V ~> K) </k>
       <env> _ => Env </env>
       <bstack> _ => Stack </bstack>
       <fstack> ([Env:Map] Stack:List, K:K) => . ...</fstack>
       [transition]

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
  rule [thread]:
       <thread>...
         <k> 'std::thread_`(_`);(T:Id,, '_`,_(F:Id,, El:Exps)) => . ...</k>
         <env> Env </env>
       ...</thread>
       (. => 
        <thread>... 
        <name> T </name>  
        <k> '_;('_`(_`)(F,, El)) </k> <env> Env </env>  
        ...</thread>
       )
  
  /*@
    A thread is finished (and deleted) when the content of its \texttt{k}
    cell is empty:
  */
  rule [thread-end] :
       (<thread>... <k>.K</k>  ...</thread> => .)


  /*@
    \subsection{Auxiliary Functions and Rules.}
    Here we winclude the semantics for the auxiliary constructs, used to give
    semnatics for \Cink.
  */

  /*@
   The function \texttt{isDeclLabel} tests whether a \K label is a declaration.
   It allows to treat the declaration in a compact way.
  */
  syntax Bool ::= "isDeclLabel" "(" KLabel ")" [function]

  rule isDeclLabel(KL:KLabel) => true
       when       KL ==KLabel 'int_
       orElseBool KL ==KLabel 'bool_ 
       orElseBool KL ==KLabel 'void_
       [anywhere]

  /*@
   The function \texttt{isDeclLabel} tests whether an initialization expression
   is in fact an alias.
  */
  syntax K ::= "isAlias" "(" Exp ")" [function]

  rule isAlias(& X:Id = E:Exp) => true [anywhere]

  /*@
   In some places we needed to test whether an expression is an l-value.
   Here is a minimal definition for such an operator:
  */
  syntax Bool ::= "isLValue" "(" Exp ")" [function]

  rule isLValue(lvalue(E:Exp)) => true [anywhere]

  rule isLValue(loc(L:Int)) => true [anywhere]

  rule isLValue(X:Id) => true [anywhere]

  rule isLValue(* X:Id) => true [anywhere]

  /*@
    The next operator returns the variable name from an expression occurring
    in a declaration:
  */
  syntax  Id ::= "getName" "(" Exp ")" [function]

  rule getName(X:Id) => X       [anywhere]
  rule getName(& X:Id) => X     [anywhere]
  rule getName(* X:Id) => X     [anywhere]
  rule getName(KL:KLabel(E:Exp)) => getName(E)
       when isDeclLabel(KL) ==Bool true
       [anywhere]
  rule getName(E1:Exp = E2:Exp) => getName(E1) [anywhere]
  rule getName(KL:KLabel('_`,_(E:Exp,, .Exps))) => getName(E)
       when isDeclLabel(KL) ==Bool true
       [anywhere]


  /*@
    The semantics of \texttt{popb} is to pop out the stack of the
    block environments:
  */
  syntax K ::= "popb"

  rule <k> popb => . ...</k>
       <bstack> [Env:Map] => . ...</bstack>
       <env> _ => Env </env> 

endmodule

/*@ \section{Modules for Model-Checking}
The \KTool includes a copy of the Maude LTL model-checker, where the sorts
and the operations were renamed to avoid name clashes and to follow the \K 
convention for naming builtin items. For instance, the sort name for the 
transition system states is \texttt{\#ModelCheckerState} and that for the 
atomic propositions is \texttt{\#Prop}.
For similar reasons, the operators for LTL formulas are prefixed with "LTL".
Since any builtin sort is subsorted to the sort \texttt{K}, it follows that 
\texttt{\#ModelCheckerState} is a  subsort of \texttt{K}. 
*/

module CINK-SYNTAX
  imports CINK-LANG-SYNTAX
  imports LTL-HOOKS

  /*@
    This module combines the syntax of the \Cink language with that of 
    the LTL formulas.
    The module \texttt{LTL-HOOKS} is a \K interface to the Maude module 
    definign the LTL syntax. In addition to this interface, we have to
    define the atomic propositions. Here is an example of such proposition,
    whose intended semantics is to test whether the value of a variable in the
    configuration is equal to a given value. The semantics for this proposition
    will be given later, in the main module.  
  */

  syntax Prop ::= "eqTo" "(" Id "," Val ")" // [function]

endmodule

module CINK
  imports MODEL-CHECKER-HOOKS
  imports CINK-SYNTAX
  imports CINK-LANG-SEMANTICS

  /*@
    This is the main module that combines the semantics of \Cink with the
    interface to the model-checker, given by the module \texttt{LTL-HOOKS}.
  */

  /*@ The states of the transition system to be model-checked are given
      by the configurations of \Cink programs, which are of sort \texttt{Bag}:
  */

  syntax #ModelCheckerState ::= "KItem" "(" Bag ")"

  /*@
   The following two constructions is a trick by which the atomic propositions
   are "hooked" by similar propositions defined over builtin sorts.
   In the future, these should be automatically generated.
  */
  syntax #Prop ::= "#eqTo" "(" Id "," Val ")" [function]
  

  rule eqTo(X:Id, V:Val) => #eqTo(X, V) [anywhere]

  /*@
    In order to give semantics to the proposition \texttt{eqTo}, we use an 
    auxiliary function \texttt{val} that returns the value of a given variable
    name in a given configuration: 
   */

  syntax Int ::= "val" "(" Bag "," Id ")" [function]

  rule val(<T>... 
                 <genv>... X:Id |-> L:Int ...</genv> 
                 <store>... L |-> I:Int ...</store> 
           ...</T>, X)
       =>
       I
       [anywhere]
  /*@
    We are ready now to give the semantics for \texttt{eqTo}$(X,I)$: it is 
    satisfied by a configuration (state) $B$ iff the value of $X$ in $B$ is
    equal to $I$: 
   */

  rule KItem(B:Bag) LTL|= #eqTo(X:Id, I:Int) => true when val(B, X) ==K I [anywhere]


endmodule


