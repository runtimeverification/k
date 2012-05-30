/*!
\setlength{\parindent}{1em}
\title{CinK -- an experiment on how to think in \K}
\author{Dorel Lucanu (\texttt{dlucanu@info.uaic.ro})}
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
      semantics. 
      Obviously, any value is an expression.
  */

  syntax LVal ::=  Int
  syntax Val ::= "cout" | "cin" | Bool | String

  syntax Exp ::= Id | Val
               | "(" Exp ")"  [bracket]
               | Id "(" Exps ")" [prec(0), strict(1)]
               | "&" Exp
               | "*" Exp [strict]
               > left:
                 Exp "*" Exp [left, strict]
               | Exp "/" Exp [left, strict]
               | Exp "%" Exp [left, strict, latex("{#1}\%{#2}")] 
               >  left:
                 Exp "+" Exp [left, strict, superheat]
               | Exp "-" Exp [left, strict]
               > left:
                 Exp ">" Exp [left, strict]
               | Exp "<=" Exp [left, strict, latex("{#1}\leq{#2}")] 
               | Exp "==" Exp [left, strict]
               >
                 "!" Exp [strict] 
               > 
                 Exp "&&" Exp [left, strict(1), latex("{#1}\&\&{#2}")]
               > 
                Exp "||" Exp [left, strict(1)]
               > left:
                 Exp "<<" Exp [left, seqstrict]
               | Exp ">>" Exp [left, strict(1)]
               >
                 Exp "=" Exp [right, strict(2)]
               

  syntax #Id ::= "main" 

  /* \subsection{Statements} */

  syntax Stmt ::= Exp ";" [strict]
               | Decl ";"
               | "{" "}"
               | "{" Stmts "}"
               | "while" "(" Exp ")" Stmt 
               | "return" Exps ";" // [strict]
               | Decl "(" Decls ")" "{" Stmts "}"
               | "#include" "<iostream>" [latex("\texttt{\#include<iostream>}")]
               | "if" "(" Exp ")" Stmt "else" Stmt [strict(1)]
               >
                 "if" "(" Exp ")" Stmt

  syntax Pgm ::= Stmts 

  /* \subsection{Lists} */

//  syntax Stmts ::= List{Stmt,""}
  syntax Stmts ::= Stmt | Stmts Stmts [left]

  syntax Exps  ::= List{Exp,  ","} [strict]
  syntax Decls ::= List{Decl, ","}


endmodule

module CINK-SEMANTICS
  imports CINK-SYNTAX

  /* \subsection{ASTs which are results.} */

  syntax Val ::= "void" 
               | "lambda" "(" Decls "@" Stmts ")" [latex("\lambda{#1}\mathrel{\bullet}{#2}")]
               | "loc" "(" Int ")"

  syntax Vals ::= List{Val,","}
  syntax KResult ::= Val

  /* \subsection{Auxiliary constructs.} */

  // extends the expressions with other constructs
  syntax Exp ::=  "lvalue" "(" K ")"
               | "valFromLoc" "(" K ")" [strict]

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
  rule '_;('bool_('_=_(X:Id,, B:Exp)))
       =>
       '__('_;(int X),, '_;('_=_(X,, B)))
       [anywhere]

  
  /* \subsection{Expressions Evaluation.} */
  rule I1:Int + I2:Int => I1 +Int I2 [structural]
  rule I1:Int - I2:Int => I1 -Int I2 [structural]
  rule '_*_(I1:Int,, I2:Int) => I1 *Int I2 [structural]
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

  rule [indirection] :
       <k> (* L:Int) => V ...</k>
       <store>... L |-> V ...</store>

  syntax  Id ::= "getName" "(" Decl ")" [function]

  rule getName(int  X:Id) => X     [anywhere]
  rule getName(bool X:Id) => X     [anywhere]
  rule getName(int  & X:Id) => X   [anywhere]
  rule getName(bool & X:Id) => X   [anywhere]
  rule getName('void_(X:Id)) => X  [anywhere]


  /* \subsection{Declarations.} */
  rule [fun-decl] :
       <k> '_`(_`)`{_`}(Decl:Decl,, Xl:Decls,, Sts:Stmts) => .  ...</k> 
       <env>... . =>  (getName(Decl) |-> L) ...</env>
       <store>... . => (L |-> lambda(Xl @ Sts)) ...</store>
       <nextLoc> L:Int => (L +Int 1) </nextLoc>
       [structural]

   rule [var-decl] :
       <k> Decl:Decl => void  ...</k>      
       <env> Env:Map => Env[L/getName(Decl)] </env>
       <store>... . => (L |-> undefined) ...</store>
       <nextLoc> L:Int => (L +Int 1) </nextLoc>
      [structural]

   rule [alias-decl] :
       <k> int & X:Id = Y:Id => void  ...</k>      
       <env> Y |-> L:Int (Env:Map => Env[L/X]) </env>
      [structural]

   rule [alias-decl] :
       <k> bool & X:Id = Y:Id => void  ...</k>      
       <env> Y |-> L:Int (Env:Map => Env[L/X]) </env>
      [structural]

  rule [include] :
       <k> #include <iostream> => .  ...</k>
       [structural]

  rule <k> execute => '_;('_`(_`)(main,, .Vals)) </k>
       <env> Env:Map </env>
       <genv> . => Env:Map </genv>
       [structural]

  /* \subsection{Memmory operations.} */


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

  rule [seq-comp] : (Sts:Stmts Sts':Stmts) => (Sts ~> Sts') [structural] 

  /* \subsection{Input/Output Statements.} */

  rule [print-stream]:
       <k> cout << V:Val => cout  ...</k>  
       <out>... . => (ListItem(V) ListItem(" ")) </out>

  rule [read-stream]:
       <k> cin >> X:Id => cin  ...</k>
       <env>...  X |-> L:Int  ...</env>
       <store>... L |-> (_ => I)  ...</store>
       <in> (ListItem(I:Int) => .)  ...</in>


  context '_`(_`)(lambda(Xl:Decls @ Sts:Stmts),, (HOLE => evaluate HOLE following Xl;))

  syntax Exps ::= "evaluate" Exps "following" Decls ";"

  context evaluate (HOLE, _:Exps) following (int X:Id, _:Decls);

  context evaluate((HOLE => lvalue(HOLE)), _:Exps) following  (int & X:Id, _:Decls);

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

  rule [return] : return .Exps ; => return void; [structural]
  context return HOLE, Es:Exps ;
  rule [return] : return V:Val, Es:Exps ; => return Es ; 
       when Es =/=K .Exps 
       [structural]

  rule [return] :
       <k> (return V:Val; ~> _) => (V ~> K) </k>
       <env> _ => Env </env>
       <bstack> _ => Stack </bstack>
       <fstack> ([Env:Map] Stack:List, K:K) => . ...</fstack>
       [supercool]

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

  // \texttt{popb} pops out the stack of block environments
  syntax K ::= "popb"

  rule <k> popb => . ...</k>
       <bstack> [Env:Map] => . ...</bstack>
       <env> _ => Env </env> 


endmodule


module CINK
  imports CINK-SEMANTICS
//  imports MODEL-CHECKER-HOOKS

endmodule

