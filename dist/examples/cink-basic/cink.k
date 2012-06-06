/*!
\setlength{\parindent}{1em}
\title{CinK -- an experiment on how to think in \K}
\author{Dorel Lucanu (\texttt{dlucanu@info.uaic.ro}) and 
        Traian Florin \c{S}erb\u{a}nu\c{t}\u{a}}
\organization{Alexandru Ioan Cuza University of Ia\c{s}i, Romania}
\newcommand{\myparagraph}[1]{\textbf{#1}}
*/

/*@ \section{Introduction}

CinK is C++ like language we used to experiment with \K. The language is used
an example for teaching classes and is refered in several research paper.

In this report we briefly present the \K definition of CinK. The most part of
the text is automatically generated with the \K tool, therefore there are some
differences btween the source code and the pdf version. For instance, the
terminal syntax declarations are enclosed into quotes but in the pdf version
these are not displayed. In pdf version, for ease reading reasons, there are 
used different fonts in order to distinguish between different syntactic 
categories.

We refer the reader to~\cite{k-primer-2012-v25} for a brief presentation of 
the \KTool.

/*@ \section{Syntax}
The syntax of Cink is written using the last version at the moment of the 
\K Tool, namely K3. The syntax of a language is given using a BNF-like 
notation enriched with annotations and priority specifications. 
*/

module CINK-SYNTAX 

  imports BUILTIN-SYNTAX-HOOKS

  /*@ \subsection{Declarations} */

  syntax Decl ::= "int"  Exp
                | "void" Id 
                | "bool" Exp

  /*@ \subsection{Expressions} */

  /*@ The constants of the builtin types are primitive constructs and therefore
      they should be values. We distinguish the subsort of "lvalues", which 
      we assume that they are integers. 
      The sort for values will be extended in the module describing the 
      semantics. The sort \texttt{LVal} is for \textit{lvalues}, i.e., those
      that designates locations. We use non-negative integers for locations,
      therefore the only constructor for \texttt{Lval} is the subsort 
      \texttt{Int}.
      We prefer to declare \texttt{cin} and \texttt{cout} as values rather 
      than identifier; the reason for this decisin will be explained later.
   */

  syntax LVal ::=  Int
  syntax Val ::= "cout" | "cin" | Bool | String | LVal 

  /*@
    We included in CinK a small subset of C++ language, the missing operators
    can be easily added in a similar way. Recall that the most important (from
    the semantic point of view) thing we have to mention for operators is the
    attribute \texttt{strict}, that specifies the evaluation order of the 
    operands. For instance, the arithmetic binary 
    operators are strict in both arguments, hence the behavior of some 
    programs could be undefined or non-determinsitic because the evaluation
    of the arguments could have side-effects. The assignment operator is strict
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
                 Exp "*" Exp [strict]
               | Exp "/" Exp [strict]
               | Exp "%" Exp [strict, latex("{#1}\%{#2}")] 
               >  left:
                 Exp "+" Exp [strict]
               | Exp "-" Exp [strict]
               > left:
                 Exp ">" Exp [strict]
               | Exp "<=" Exp [strict, latex("{#1}\leq{#2}")] 
               | Exp "==" Exp [strict]
               >
                 "!" Exp [strict] 
               > 
                 Exp "&&" Exp [left, strict(1), latex("{#1}\&\&{#2}")]
               > 
                Exp "||" Exp [left, strict(1)]
               > left:
                 Exp "<<" Exp [seqstrict]
               | Exp ">>" Exp [strict(1)]
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
    
   */

  syntax Stmt ::= Exp ";" [strict]
               | "#include" "<iostream>" 
                 [latex("\texttt{\#include<iostream>}")]
               | "using" "namespace" "std" ";" 
                 [latex("using namespace std;")]
               | Decl ";"
               | "{" "}"
               | "{" Stmts "}"
               | "while" "(" Exp ")" Stmt 
               | "return" Exps ";" // [strict]
               | Decl "(" Decls ")" "{" Stmts "}"
               | "if" "(" Exp ")" Stmt "else" Stmt [strict(1)]
               >
                 "if" "(" Exp ")" Stmt
  /*@
    A program is a sequence of statements.
  */
  syntax Pgm ::= Stmts 

  /* \subsection{Lists} */

//  syntax Stmts ::= List{Stmt,""}
  syntax Stmts ::= Stmt | Stmts Stmts [left]

  syntax Exps  ::= List{Exp,  ","} [strict]
  syntax Decls ::= List{Decl, ","}

endmodule

module CINK-SEMANTICS
  imports CINK-SYNTAX

  /*@ \subsection{Values.} 
    The values are a very important syntactic category in the definition
    of any languages; with them, we are able to know when the evaluation
    of an expression is finished. This piece of information is crucial, e.g.,
    for the heating and cooling rules. "Paradoxally", the value \texttt{void}
    means in fact "no value". The lambda abstractions are used for storing the
    functions. Similar to other \K examples (IMP. IMPPP, SIMPLE), the 
    functions are stored similar to variables and therefore their definitions
    are seen as values. The values of the form \texttt{loc($L$:Int)} designate
    locations and they are used as result for the evaluation of the l-values.
    As usual, all values must be subsorted to the \texttt{KResult} sort.
   */

  syntax Val ::= "void" 
               | "lambda" "(" Decls "@" Stmts ")" 
                 [latex("\lambda{#1}\mathrel{\bullet}{#2}")]
               | "loc" "(" Int ")"

  syntax Vals ::= List{Val,","}
  syntax KResult ::= Val

  /* \subsection{Auxiliary constructs.} */

  /*@
    In some contexts, some expressions are evaluated to l-values.
    We wrap these expressions with the \texttt{lvalue} tag.
  */
  syntax Exp ::=  "lvalue" "(" K ")"

  syntax K ::= "undefined" | "execute"

  syntax ListItem ::= "(" List "," K ")"
                    | "[" Map "]"

 /* \subsection{Configuration.} */
  configuration <T color="yellow">
                  <k color="green"> ($PGM:Pgm ~> execute) </k>
                  <env color="LightSkyBlue"> .Map </env>
                  <fstack color="orange"> .List </fstack>
                  <bstack color="orange"> .List </bstack>
                  <genv color="SkyBlue"> .Map </genv>
                  <store color="white"> .Map </store>
//                  <br/>
                  <in color="magenta" stream="stdin"> $IN:List </in>
//                  <out color="Orchid"> .List </out>
                  <out color="Orchid" stream="stdout"> .List </out>
                  <nextLoc> 0 </nextLoc>
                </T>

// macros
  rule if(B:Exp) St:Stmt => if(B) St else {}  [anywhere]
  rule '_`(_`)(X:Id,,E:Exp) => '_`(_`)(X,,'_`,_(E,, .Exps))  [anywhere]
  rule void X:Id => int X  [anywhere]
  rule '_;('int_('_=_(X:Id,, A:Exp)))
       =>
       '__('_;(int X),, '_;('_=_(X,, A)))
       [anywhere]
  rule '_;('int_('_=_(*X:Id,, A:Exp)))
       =>
       '__('_;(int X),, '_;('_=_(X,, A)))
       [anywhere]
  rule '_;('bool_('_=_(X:Id,, B:Exp)))
       =>
       '__('_;(int X),, '_;('_=_(X,, B)))
       [anywhere]

  
  /* \subsection{Expressions Evaluation.} */
  rule I1:Int + I2:Int => I1 +Int I2 [structural]
  rule I1:Int - I2:Int => I1 -Int I2 [structural]
  rule '_*_(I1:Int,, I2:Int) => I1 *Int I2 [structural]
//  rule I1:Int * I2:Int => I1 *Int I2 [structural]
  rule I1:Int / I2:Int => I1 /Int I2 when I2 =/=Int 0 [structural]
  rule I1:Int % I2:Int => I1 %Int I2 when I2 =/=Int 0 [structural]

  rule I1:Int > I2:Int => (I1 >Int I2) [structural]
  rule I1:Int <= I2:Int => (I1 <=Int I2) [structural]
  rule I1:Int == I2:Int => (I1 ==Int I2) [structural]
 
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

  //@ The dereferencing operator .
  context & (HOLE => lvalue(HOLE))
  rule & loc(L:Int) => L


  /*@ \subsubsection{The prefix increment operator.}
    From the standard:
    "The operand of prefix ++ is modified by adding 1, or set to true 
    if it is bool (this use is deprecated). The operand shall be a 
    modifiable lvalue. The type of the operand shall be an arithmetic 
    type or a pointer to a completely-defined object type. 
    The result is the updated operand; it is an lvalue, and it is a 
    bit-field if the operand is a bit-field."
    This raises some problems. We suppose that we want to evaluate the
    expression \texttt{y + (++x)}; since the addition operator is strict in 
    both arguments, it will be reduced something like $\it I + loc(L)$ and 
    in that case $\it loc(L)$ should be evaluate at the value stored into
    the location $L$.
  */

  context ++ (HOLE => lvalue(HOLE))
  rule <k> ++ loc(L) => loc(L) ...</k>
       <store>... L |-> (V:Int => V +Int 1) ...</store>

  /*@
    Here we try to identify the contexts under which an l-value is 
    transformed into an r-value.
  */ 
  syntax K ::= "rvalue" "(" K ")"

  syntax Bool ::= "hasRValueArgs" "(" KLabel ")"

  rule hasRValueArgs(OP:KLabel) => true
    when       OP ==KLabel '_+_ 
    orElseBool OP ==KLabel '_-_ 
    orElseBool OP ==KLabel '_*_ 
    orElseBool OP ==KLabel '_/_ 
    orElseBool OP ==KLabel '_%_ 
    orElseBool OP ==KLabel '_<_ 
    orElseBool OP ==KLabel '_<=_
    orElseBool OP ==KLabel '_||_
    orElseBool OP ==KLabel '_<<_ 
    orElseBool OP ==KLabel '_>>_  
    [anywhere]


  rule [Lval2Rval1stArg] :
       <k> OP:KLabel((loc(L:Int) => V),,_:List{K}) ...</k>
       <store>... L |-> V:Val ...</store>
    when hasRValueArgs(OP) ==K true

  rule [Lval2Rval2ndArg] :
       <k> OP:KLabel(_:List{K},, (loc(L:Int) => V)) ...</k>
       <store>... L |-> V:Val ...</store>
    when hasRValueArgs(OP) ==K true

  rule [Lval2RvalAssg] :
       <k> loc(L1:Int) = (loc(L2:Int) => V) ...</k>
       <store>... L2 |-> V:Val ...</store>


/*
  rule <k> loc(L:Int) + V:Val => rvalue(loc(L:Int)) + V:Val ...</k>
       <store>... L |-> V:Val ...</store>

  rule <k> cout << loc(L:Int) => cout << rvalue(loc(L:Int)) ...</k>
       <store>... L |-> V:Val ...</store>

  rule <k> rvalue(loc(L:Int)) => V ...</k>
       <store>... L |-> V:Val ...</store>
*/

  syntax  Id ::= "getName" "(" Decl ")" [function]

  rule getName(int  X:Id) => X     [anywhere]
  rule getName(bool X:Id) => X     [anywhere]
  rule getName(int  & X:Id) => X   [anywhere]
  rule getName(bool & X:Id) => X   [anywhere]
  rule getName(int  * X:Id) => X   [anywhere]
  rule getName(bool * X:Id) => X   [anywhere]
  rule getName('void_(X:Id)) => X  [anywhere]


  /* \subsection{Declarations.} */
  rule [fun-decl] :
       <k> '_`(_`)`{_`}(Decl:Decl,, Xl:Decls,, Sts:Stmts) => .  ...</k> 
       <env>... . =>  (getName(Decl) |-> L) ...</env>
       <store>... . => (L |-> lambda(Xl @ Sts)) ...</store>
       <nextLoc> L:Int => (L +Int 1) </nextLoc>
       [structural]

  /*@
    The rules vor variable declarations must be in this order.
  */

  context int & X = (HOLE => lvalue(HOLE))
  rule [alias-decl] :
       <k> int & X:Id = loc(L:Int) => void  ...</k>      
       <env> Env:Map => Env[L/X] </env>
       [structural]

  rule [alias-decl] :
       <k> bool & X:Id = Y:Id => void  ...</k>      
       <env> Y |-> L:Int (Env:Map => Env[L/X]) </env>
       [structural]

  rule [var-decl] :
       <k> Decl:Decl => void  ...</k>      
       <env> Env:Map => Env[L/getName(Decl)] </env>
       <store>... . => (L |-> undefined) ...</store>
       <nextLoc> L:Int => (L +Int 1) </nextLoc>
       [structural]

  rule [include] :
       <k> #include <iostream> => .  ...</k>
       [structural]

  rule [include] :
       <k> using namespace std;=> .  ...</k>
       [structural]

  rule <k> execute => '_;('_`(_`)(main,, .Vals)) </k>
       <env> Env:Map </env>
       <genv> . => Env:Map </genv>
       [structural]

  /* \subsection{Memmory operations.} */

  context lvalue(HOLE) when 'isId(HOLE) =/=K true

  rule lvalue(L:Int) => loc(L) [structural]

  rule lvalue(loc(L:Int)) => loc(L) [structural]

  rule [mem-lookup-lvalue] :
       <k> lvalue(X:Id) => loc(L) ...</k>
       <env>... X |-> L:Int ...</env>

  rule [mem-lookup-lvalue-indirect] :
       <k> lvalue(* X:Id) => loc(V) ...</k>
       <env>... X |-> L:Int ...</env>
       <store>... L |-> V:Val ...</store>

  rule [mem-lookup-rvalue] :
       <k> X:Id => V ...</k>
       <env>... X |-> L:Int ...</env>
       <store>... L |-> V:Val ...</store>

  context (HOLE => lvalue(HOLE)) = _
  rule [mem-update] :
       <k> loc(L:Int) = V:Val => V  ...</k>
       <env>...  X |-> L  ...</env>
       <store>... L |-> (_ => V) ...</store>

  /* \subsection{Control Statements.} */
  rule [while] :
       while(B:Exp) St:Stmt => if (B) {St while(B) St} else {}
       [structural]

  rule [if-false] : if(false) _ else St:Stmt => St
  rule [if-true] : if(true) St:Stmt else _ => St

  rule [instr-expr] : 
       <k> (V:Val; ~> K:K) => K </k> 
       when K =/=K .K
//       [transition]

  rule [block] : 
       <k>{Sts:Stmts} => (Sts ~> popb)  ...</k>
       <env> Env:Map </env>
       <bstack> . => [Env] ...</bstack>
       [structural]

  rule [block-empty] : {} => .  [structural]

  rule [seq-comp] : 
       (Sts:Stmts Sts':Stmts) => (Sts ~> Sts')
       [structural] 

  /* \subsection{Input/Output Statements.} */

  rule [print-stream]:
       <k> cout << V:Val => cout  ...</k>  
       <out>... . => (ListItem(V) ListItem(" ")) </out>

  rule [read-stream]:
       <k> cin >> X:Id => cin  ...</k>
       <env>...  X |-> L:Int  ...</env>
       <store>... L |-> (_ => I)  ...</store>
       <in> (ListItem(I:Int) => .)  ...</in>


  context '_`(_`)(lambda(Xl:Decls @ Sts:Stmts),, 
                 (HOLE => evaluate HOLE following Xl;))

  syntax Exps ::= "evaluate" Exps "following" Decls ";"

  context evaluate (HOLE, _:Exps) following (int X:Id, _:Decls);

  context evaluate((HOLE => lvalue(HOLE)), _:Exps)
          following  (int & X:Id, _:Decls);

  rule evaluate(V:Val, El:Exps) following (Dec:Decl, Xl:Decls);
    => V, evaluate El following Xl;
  rule evaluate .Exps following .Decls; => .Vals


  /* \subsection{Function Call.} */
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

  /* \subsection{Function Return.} */

  rule [return] : return .Exps ; => return void; [transition]
  context return HOLE, Es:Exps ;
  rule [return] : return V:Val, Es:Exps ; => return Es ; 
       when Es =/=K .Exps 
       [transition]

  rule [return] :
       <k> (return V:Val; ~> _) => (V ~> K) </k>
       <env> _ => Env </env>
       <bstack> _ => Stack </bstack>
       <fstack> ([Env:Map] Stack:List, K:K) => . ...</fstack>
       [transition]

  /* \subsection{Auxiliary Functions and Rules.} */


  // \texttt{bindto} binds formal parameters to actual parameters 

  syntax K ::= "bind" Vals "to" Decls ";"  


  rule <k> bind((V:Val, Vs:Vals) => Vs)
           to((int X:Id, Xl:Decls) => Xl); 
       ...</k>
       <env> Env:Map => Env[L/X] </env>
       <store>... . => L |-> V ...</store>
       <nextLoc> L:Int => L +Int 1 </nextLoc>

  rule <k> bind((loc(L:Int), Vs:Vals) => Vs)
           to((int & X:Id, Xl:Decls) => Xl); 
       ...</k>
       <env> Env:Map => Env[L/X] </env> 

  rule bind .Vals to .Decls; => . [ structural ]

  //@ \texttt{popb} pops out the stack of block environments
  syntax K ::= "popb"

  rule <k> popb => . ...</k>
       <bstack> [Env:Map] => . ...</bstack>
       <env> _ => Env </env> 

endmodule


module CINK
  imports CINK-SEMANTICS
//  imports MODEL-CHECKER-HOOKS

endmodule


