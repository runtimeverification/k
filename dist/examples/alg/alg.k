/*!
\setlength{\parindent}{1em}
\title{Alg -- an experimental algorithmic language in \K}
\author{Dorel Lucanu (\texttt{dlucanu@info.uaic.ro})}
\organization{Alexandru Ioan Cuza University of Ia\c{s}i, Romania}
\usepackage{alltt}
\newcommand{\myparagraph}[1]{\textbf{#1}}
\newcommand{\KTool}{\K tool\xspace}
\newcommand{\Cpp}{\mbox{C\raisebox{.2ex}{\small\!+\!+}}\xspace}
*/

/*@ \section{Introduction}
This file include the definition of an algorithmic language, intended to be used for teaching data structures and algorithms using an abstraction notation (independent of programming language).

We intend to add tools supporting algorithm analysis (e.g., the computation of the worst-case time complexity).
*/

/*@ 
\section{Syntax}

*/

module ALG-SYNTAX
 
  syntax Val ::=  Bool | Int | Float | String

  syntax Name ::= Id | Id "::" Id 

  syntax Exp ::= Val | Name
               | "(" Exp ")"  [bracket]
               | Name "(" Exps ")" [strict(1)]
               |  Name "[" Exp "]" [strict]
               > right:
                 Exp "." Exp [right]
               > "-" Exp [strict]
               > left:
                 Exp "*" Exp [left, strict]
               | Exp "/" Exp [left, strict]
               | Exp "%" Exp [left,strict]
               > left:
                 Exp "+" Exp [left, strict]
               | Exp "-" Exp [left, strict]
               > left:
                 Exp "<" Exp [left, strict]
               | Exp "<=" Exp [left, strict]
               | Exp ">" Exp [left,strict]
               | Exp ">=" Exp [left, strict]
               | Exp "!=" Exp [left,strict]
               | Exp "==" Exp [left,strict]
               > "!" Exp [strict]
               > left:
                 Exp "&&" Exp [left, strict]
               | Exp "||" Exp [left, strict]
               | Exp "=>" Exp [left, strict]

  syntax Stmt ::= Exp "=" Exp ";" [strict(2)]
               | Exp ";" [strict]
               | "{" "}"
               | "{" Stmts "}"
               | "while" "(" Exp ")" Stmt 
               | "return" Exps ";" [strict]
               | Exp "(" Ids ")" "{" Stmts "}"
               | "if" "(" Exp ")" Stmt "else" Stmt [strict(1)]
               >
                 "if" "(" Exp ")" Stmt

  syntax Stmts ::= Stmt | Stmts Stmts [left]

  syntax Ids  ::= List{Id,  ","} [strict]
  syntax Exps  ::= List{Exp,  ","} [strict]

endmodule

/*@

\section{Semantics}

*/

module ALG 
  imports ALG-SYNTAX 


  rule if(B:Exp) St:Stmt => if(B) St else {} 

/*@
\subsection{Values}
The values are the most important in the representation of the states.  
The values together with their operations they define the computation model for the algorithm represented in the language.

We distinguish two categories of values:
\begin{list}{}{3ex}
\item[\it Scalars (primitive values)] These are booleans, integers, rationals (floats), and strings. For the operations of these types we may have two measurement 
\item[\it Structured values] These are cons lists, arrays, structures. 
\end{list} 

\subsubsection{Cons Lists}
Con lists are also called "lists \'a la Lisp". They have a recursive definition:
\begin{itemize}
\item the empty lists is a cons list;
\item if $V$ is a value and $L$ is a list the $V, L$ is a cons list (this is the cons 
(from constructor) operation). 
\end{itemize}
a list with three elements is represented as $a, (b, (c, ()))$.



In \K the cons lists are declared as:
\begin{alltt}
  syntax Vals ::= List\{Val,","\}
\end{alltt}
The empty list (as value) is \texttt{.Vals}. The operations include:

\indent\begin{tabular}{ll}
Operation & Time Complexity\\
\tt lookup(i) & $O(i)$\\
\tt insert(i, x) & $O(i)$\\
\tt update(i, x) & $O(i)$\\
\tt topFront() & $O(1)$\\
\tt pushFront(x) & $O(1)$\\
\tt topBack() & $O(size(L))$\\
\tt pushBack() & $O(size(L))$\\
\end{tabular}

\noindent
where $L$ is the list which the operation is executed over. 

\subsubsection{Arrays}
An array is represented as a finite set of maps from indexes to values.
For instance, the array with three elements $a,b,c$ is represented as 
$\{0\mapsto a~ 1\mapsto b~ 2\mapsto c\}$.
The basic operations are \texttt{lookup(i)} and \texttt{update(i,x)}, 
both having the time complexity $O(1)$.

\subsubsection{Structures}

The structures are represented in a similar way as the arrays, but the maps are from 
fields names to values.
For instance, a structure representing points in plane has two fields: \texttt{x} and \texttt{y}. 
Hence the point $(2,7)$ is represented by the structure 
$\{\texttt{x}\mapsto 2~\texttt{y}\mapsto 7\}$.

These definitions for values can be used to represent complex data structures. 
For example, the graph 
$G=(\{0,1,2\}, \{(0,1), (0,2), (1,2)\})$ is represented by adjacency lists as follows:\\
$\{\texttt{n}\mapsto 3~ \texttt{a}\mapsto \{0\mapsto [1,2,\texttt{.Vals}]~
1\mapsto [0,2,\texttt{.Vals}]~2\mapsto [0,1,\texttt{.Vals}]\}\}$,\\
 where $[a_0,a_1,\ldots]$ is a list (see below).
*/

  syntax Val ::= "noVal" 
               | "lambda" "(" Ids "@" Stmts ")" 
                 [latex(\lambda\,{#1}\mathrel{\bullet}{#2})]
               | "[" Vals "]" [kalbel("absList")]
               | "{" Map "}"  [klabel("structOrArray")]

  syntax Vals ::= List{Val,","}
  syntax KResult ::= Val

/*
\subsection{Configuration}

The configuration is very simple. It includes only two cells: one for local variables and the other one 
for global variables, useful for function calls (inclusive recursive functions).
The content of each of the two cells is a set of maps $\textit{variable-name}\mapsto \textit{value}$, 
abstracting the memory.

EXamples: a map $\texttt{x}\mapsto 5$ represents a memory cell storing $5$ and refered by \texttt{x}:
\[

\]
*/

  configuration 
    <k> copyGlobalState; ~> $PGM:Stmts </k>
    <state> $ST:Map </state>
    <gstate multiplicity="?"> $GST:Map </gstate>

  syntax Stmt ::= "copyGlobalState;"

  rule <k> copyGlobalState; => . ...</k>
       <state>... . => GSt ...</state>
       <gstate>  GSt:Map </gstate>


  rule <k> .K </k>
       (<gstate> _:Map </gstate> => .)

  rule <k>  '_`(_`)`{_`}(F:Name,, Xl:Ids,, Sts:Stmts)  => .  ...</k> 
       <state>... . => (F |-> lambda(Xl @ Sts)) ...</state>
       <gstate>... . => (F |-> lambda(Xl @ Sts)) ...</gstate>
       [fun-decl, structural]


  rule I1:Int + I2:Int => I1 +Int I2 [plus]

  rule I1:Int - I2:Int => I1 -Int I2 

  rule I1:Int * I2:Int => I1 *Int I2 

  rule I1:Int / I2:Int => I1 /Int I2 when I2 =/=Int 0 
 
  rule I1:Int % I2:Int => I1 %Int I2 when I2 =/=Int 0 

  rule I1:Int < I2:Int => (I1 <Int I2) 

  rule I1:Int > I2:Int => (I1 >Int I2) 

  rule I1:Int <= I2:Int => (I1 <=Int I2) 

  rule I1:Int == I2:Int => (I1 ==Int I2) 

  rule F1:Float + F2:Float => F1 +Float F2 [plus]


  rule F1:Float - F2:Float => F1 -Float F2 

  rule F1:Float * F2:Float => F1 *Float F2 

  rule F1:Float / F2:Float => F1 /Float F2 when F2 =/=Float 0.0 
 
  rule F1:Float % F2:Float => F1 %Float F2 when F2 =/=Float 0.0 

  rule F1:Float < F2:Float => (F1 <Float F2) 

  rule F1:Float > F2:Float => (F1 >Float F2) 

  rule F1:Float <= F2:Float => (F1 <=Float F2) 

  rule F1:Float == F2:Float => (F1 ==Float F2) 


  rule true && B:Exp => B 

  rule false && B:Exp => false 

  rule true || B:Exp => true 

  rule false || B:Exp => B 

  rule ! false  => true 

  rule ! true => false 


  rule S1:String + S2:String => S1 +String S2 


  rule <k> X:Name => V ...</k>
       <state>... X |-> V:Val ...</state>
       [lookup]

  rule <k> X:Name = V:Val; => .  ...</k>
       <state> ST => ST[V / X] </state>
       [update]


  rule while(B:Exp) St:Stmt => if (B) {St while(B) St} else {}
       [while, structural]

  rule if(false) _ else St:Stmt => St [if-false]
  rule if(true) St:Stmt else _ => St [if-true]



  rule { Sts:Stmts } => Sts
       [block, structural]

  rule {} => .  [block-empty, structural]

  rule (Sts:Stmts Sts':Stmts) => (Sts ~> Sts')
       [seq-comp, structural] 


  //@ Arrays

  context '_._(_:Name[HOLE],, _:Exp)
  context '_._(_:Exp,, _:Name[HOLE])
  context '_._(_:Exp,, '_._(_:Name[HOLE],, _:Exp))

  context _:Name[HOLE] = _:Exp;
  context '_._(_:Exp,, _:Name[HOLE]) = _:Exp;
  context '_._(_:Exp,, '_._(_:Name[HOLE],, _:Exp)) = _:Exp;


  // lookup
  rule '_`[_`]({_ I |-> V:Val _},, I:Int) => V

  // update
  rule <k> X:Name[I:Int] = V:Val ; => . ...</k>
       <state>... X |-> (Vx:Val => update(Vx, I, V)) ...</state>


  // structure fields

  context '_._(HOLE,, E:Exp) when isFieldName(E)

  // lookup
  rule '_._(V:Val,, E:Exp) => lookup(V, E) when isFieldName(E)

  // update
  rule <k> '_._(X:Name,, E:Exp) = V:Val ; => . ...</k>
       <state>... X |-> (Vx:Val => update(Vx, E, V)) ...</state>
       when isFieldName(E)



  // method call

  syntax #Id ::= "self"

  syntax K ::= "updateSelf" "(" Id "," Exp ")" [strict(2)]


  rule <k> ('_._(L:Id,, F:Name (El:Exps)))
           =>
           evaluate (L, El) to .Vals following (self, Xl)::Ids; ~> updateSelf(L, self) ~>
           '_`(_`)(lambda(Xl:Ids @ Sts:Stmts),, HOLE)
       ...</k>
       <state>... F |-> lambda(Xl:Ids @ Sts:Stmts) ...</state>
       [meth-call]

  rule <k> ('_._(L:Id,, F:Id (El:Exps)))
           =>
           evaluate (L, El) to .Vals following (self, Xl); ~> updateSelf(L, self) ~>
           '_`(_`)(lambda(Xl:Ids @ Sts:Stmts),, HOLE)
       ...</k>
       <state> St:Map Str:Id :: F |-> lambda(Xl:Ids @ Sts:Stmts) </state>
       when notBool (F in keys(St))
       [meth-call]

  rule <k> (Vl:Vals ~>  updateSelf(L:Id, self) ~> '_`(_`)(lambda(Xl:Ids @ Sts:Stmts),, HOLE) ~> K:K)
           => 
           (bind Vl to (self, Xl); ~> Sts ~> updateSelf(L, self) ~> restore(St, K))
       </k>
       <state> St:Map => mergeMap(GSt, St, GSt) </state>
       <gstate> GSt:Map </gstate>
       [meth-call]

  rule <k> (return V:Val;  ~> updateSelf(L, Self:Val) ~> restore(St:Map, K:K))
           =>
          (V ~> K)
       </k>
       <state> St':Map => mergeMap(St[Self/L], St'[Self/L], GSt) </state>
       <gstate> GSt:Map => mergeMap(GSt, St'[Self/L], GSt) </gstate>
       [meth-return]

  rule <k> (updateSelf(L, Self:Val) ~> restore(St:Map, K:K))
           =>
          (noVal ~> K)
       </k>
       <state> St':Map => mergeMap(St[Self/L], St'[Self/L], GSt) </state>
       <gstate> GSt:Map => mergeMap(GSt, St'[Self/L], GSt) </gstate>
       [meth-return]

  // function call
  rule <k> '_`(_`)(lambda(Xl:Ids @ Sts:Stmts),, El:Exps)
           =>
           evaluate El to .Vals following Xl; ~>
           '_`(_`)(lambda(Xl:Ids @ Sts:Stmts),, HOLE)
       ...</k> 
       [fun-call, structural]

  syntax K ::= "restore" "(" Map "," K ")" 

  rule <k> (Vl:Vals ~> '_`(_`)(lambda(Xl:Ids @ Sts:Stmts),, HOLE) ~> K:K)
           => 
           (bind Vl to Xl; ~> Sts ~> restore(St, K))
       </k>
       <state> St:Map => mergeMap(GSt, St, GSt) </state>
       <gstate> GSt:Map </gstate>
       [fun-call]


  syntax Exps ::= "evaluate" Exps "to" Vals "following" Ids ";"


  context evaluate (HOLE, _:Exps) to _:Vals following (X:Id, _:Ids);

  rule evaluate(V:Val, El:Exps => El)
       to (Vl:Vals => '_._(Vl,, pushBack(V)))
       following (FP:Id, Xl:Ids => Xl);
       [structural]
   
  rule evaluate .Exps to Vl:Vals following .Ids; => Vl [structural]

  syntax K ::= "bind" Vals "to" Ids ";"  

  // cal by value
  rule <k> bind((V:Val, Vs:Vals) => Vs)
           to((X:Id, Xl:Ids) => Xl); 
       ...</k>
       <state> St:Map => St[V/X] </state>
       [structural]

  rule bind .Vals to .Ids; => . [ structural ]

  // return
  rule <k> (return V:Val; ~> restore(St:Map, K:K)) => (V ~> K) </k>
       <state> St':Map => mergeMap(St, St', GSt) </state> 
       <gstate> GSt:Map </gstate> 
//       <gstate> GSt:Map => mergeMap(GSt, St', GSt) </gstate>   
       [return]

  rule <k> restore(St:Map, K:K) => (noVal ~> K) </k>
       <state> St':Map => mergeMap(St, St', GSt) </state>
       <gstate> GSt:Map </gstate>
//       <gstate> GSt:Map => mergeMap(GSt, St', GSt) </gstate>
       [return]

  rule noVal ; => .

/*@

\subsection{Lists}
This is the first example of abstract data type implemented in our language (computation model).
The objects are sequences of values: $[v_0,\ldots,v_{n-1}]$. The oprations are the usual ones: 
\texttt{empty()}, \texttt{topFront()}, \texttt{topBack()}, \texttt{select(i)}, \texttt{insert(i,x)},
 \texttt{size()}, \texttt{popFront()}, \texttt{popBack()}, \texttt{pushFront(x)}, 
\texttt{pushBack(x)}, \texttt{update(i,x)}. 

In the representation of the algorithms in our language only scalars, lists, arrays, and structures 
are used.  The cons lists have no representation at the high level.

The lists can be implemented with conslists, 
$[v_0, (v_1,(\ldots (v_{n-1}, \texttt{.Vals})\ldots))]$, 
or with structures and arrays: 
$\{\texttt{length}\mapsto n~ \texttt{arr}\mapsto \{0\mapsto v_0~ \ldots n{-}1\mapsto v_{n-1}\}\}$.
The efficiency of the operations is depending on the algorithms implementing them.

The (extended) language includes only an implementation with cons lists, described below.

*/

  syntax #Id ::= "empty" | "topFront" | "topBack" | "select" | "insert" | "size" 
               | "popFront" | "popBack" | "pushFront" | "pushBack" | "update"

/*@
Empty list:\\
$\texttt{empty()}\Rightarrow [.Vals]$\\
Time complexity: $O(1)$
*/
  
  rule isVal(empty) => true [anywhere]

  rule '_`(_`)(empty,, .Exps) => [.Vals]

/*@
Top front:\\
$\texttt{topFront}([v_0,\ldots])\Rightarrow v_0$\\
Time complexity: $O(1)$
*/

  context '_._(HOLE,, topFront(.Vals))
  rule '_._([V:Val, Vl:Vals],, topFront(.Vals)) => V

/*@
Top back:\\
$\texttt{topBack}([v_0,\ldots,v_{n{-}1}])\Rightarrow \texttt{topBack}(v_0,\ldots,v_{n{-}1})$\\
Time complexity: $O(size(L))$ (inherited from cons lists)
*/

  context '_._(HOLE,, topBack(.Vals))
  rule '_._([Vl:Vals],, topBack(.Vals)) => ['_._(Vl:Vals,, topBack(.Vals))]

/*@
Insert:\\
$\texttt{insert}([v_0,\ldots,v_{n{-}1}],i,v)\Rightarrow [\texttt{insert}((v_0,\ldots,v_{n{-}1}),i,v)]$\\
Time complexity: $O(i)$ (inherited from cons lists)
*/

  context '_._(_,, insert(HOLE:Exp, _:Exp))
  context '_._(_,, insert(_:Exp, HOLE:Exp))

  rule <k> '_._(L:Name,, insert(I:Int, V:Val)); => noVal ...</k>
       <state>... L |-> [Vl => '_._(Vl,, insert(I, V))] ...</state>

/*@
Size:\\
$\texttt{size}(v_i,\ldots)\Rightarrow \texttt{size}(v_{i{+}1},\ldots)+1$\\
$\texttt{size}(\texttt{.Vals})\Rightarrow 0$\\
Time complexity: $O(size(L))$
*/

  context '_._(HOLE,, size(.Vals))
  rule '_._([.Vals],, size(.Vals)) => 0
  rule '_._([V:Val, Vl:Vals],, size(.Vals))
       => 
       '_._([Vl:Vals],, size(.Vals)) + 1

/*@
Pop front:\\
$\texttt{popFront}([v_0,v_1,\ldots])\Rightarrow [v_1,\ldots]$\\
Time complexity: $O(1)$
*/

  rule <k> '_._(L:Name,, popFront(.Vals)) => noVal ...</k>
       <state>... L |-> [(V:Val, Vl:Vals) => Vl] ...</state>

//@ trick - I must find a general solution!!!

  rule <k> '_._(L:Name[I:Int],, popFront(.Vals)) => noVal ...</k>
       <state>... L |-> {_ I |-> [(V:Val, Vl:Vals) => Vl] _} ...</state>

/*@
Pop back:\\
$\texttt{popBack}([v_0,\ldots,v_{n{-}1}])\Rightarrow [\texttt{popBack}(v_0,\ldots,v_{n{-}1})]$\\
Time complexity: $O(size(L))$ (inherited from cons lists)
*/

  rule <k> '_._(L:Name,, popBack(.Vals)) => noVal ...</k>
       <state>... L |-> [Vl:Vals => '_._(Vl,, popBack(.Vals))] ...</state>

/*@
Push front:\\
$\texttt{pushFront}([v_0,v_1,\ldots],v)\Rightarrow [v,v_0,\ldots]$\\
Time complexity: $O(1)$
*/

  context '_._(_,, pushFront(HOLE))

  rule <k> '_._(L:Name,, pushFront(V:Val)) => noVal ...</k>
       <state>... L |-> [Vl:Vals => (V, Vl)] ...</state>

/*@
Push back:\\
$\texttt{pushBack}([v_0,\ldots,v_{n{-}1}],v)\Rightarrow [\texttt{pushBack}((v_0,\ldots,v_{n{-}1}),v)]$\\
Time complexity: $O(size(L))$ (inherited from cons lists)
*/

  context '_._(_,, pushBack(HOLE))

  rule <k> '_._(L:Name,, pushBack(V:Val)) => noVal ...</k>
       <state>... L |-> [Vl:Vals => '_._(Vl,, pushBack(V))] ...</state>

/*@
Select and Lookup (two names for the same operation):\\
select is used at high level, in algorithms.\\
Lookup is used for compatibility with the other values: arrays and structures.\\
$\texttt{select}([v_0,\ldots,v_{n{-}1}], i)\Rightarrow \texttt{lookup}((v_0,\ldots,v_{n{-}1}),i)$\\
$\texttt{lookup}([v_0,\ldots,v_{n{-}1}])\Rightarrow \texttt{lookup}((v_0,\ldots,v_{n{-}1}),i)$\\
Time complexity: $O(i)$ (inherited from cons lists)
*/

  context '_._(HOLE,, select(_))
  context '_._(_,, select(HOLE))


  rule '_._([Vl:Vals],, select(I:Int)) => lookup([Vl], I)
  rule lookup([V:Val, Vl:Vals], 0) => V
  rule lookup([V:Val, Vl:Vals], I:Int)
       => 
       lookup([Vl:Vals], I -Int 1)
       when I >Int 0

/*@
Update:\\
$\texttt{update}([v_0,\ldots,v_{n{-}1}],i,v)\Rightarrow [\texttt{update}((v_0,\ldots,v_{n{-}1}),i,v)]$\\
Time complexity: $O(i)$ (inherited from cons lists)
*/

  context '_._(_,, update(HOLE:Exp, _:Exp))
  context '_._(_,, update(_:Exp, HOLE:Exp))

  rule <k> '_._(L:Name,, update(I:Int, V:Val)) => noVal ...</k>
       <state>... L |-> [Vl => '_._(Vl,, update(I, V))] ...</state>


//@ \subsection{Operations on Cons Lists}

/*@
Insert:\\
$v_0,\ldots,\texttt{insert}((v_j,\ldots), i,v)\Rightarrow v_0,\ldots,v_j\texttt{insert}((v_{j{+}1},\ldots),i{-}1,v)$ if $i>0$\\
$v_0,\ldots,v_{i{-}1},\texttt{insert}((v_i,\ldots),0,v)\Rightarrow (v_0,\ldots,v_{i{-}1},v,v_i,\ldots)$\\
Time complexity: $O(i)$
*/

  rule '_._(Vl:Vals,, insert(0, V:Val)) => (V, Vl) [anywhere]
  rule '_._((V:Val, Vl:Vals),, insert(I:Int, V':Val))
       => 
       '_`,_(V,, '_._(Vl:Vals,, insert(I -Int 1, V')))
       when I >Int 0
      [anywhere]

/*@
Top back:\\
$\texttt{topBack}(v_i,\ldots)\Rightarrow \texttt{topBack}(v_{i{+}1},\ldots)$\\
$\texttt{topBack}(v_{n{-}1},\texttt{.Vals})\Rightarrow v_{n{-}1}$\\
Time complexity: $O(size(L))$
*/

  rule '_._((V:Val, .Vals),, topBack(.Vals)) => V [anywhere]
  rule '_`,_((V:Val, (V':Val, Vl:Vals)),, topBack(.Vals))
       => 
       '_._((V', Vl:Vals),, topBack(.Vals))
       [anywhere]

/*@
Pop back:\\
$v_0,\ldots,\texttt{popBack}(v_i,\ldots)\Rightarrow v_0,\ldots,v_i,\texttt{popBack}(v_{i{+}1},\ldots)$\\
$v_0,\ldots,v_{n{-}2}\texttt{popBack}(v_{n{-}1},\texttt{.Vals})\Rightarrow v_0,\ldots,v_{n{-}2}$\\
Time complexity: $O(size(L))$
*/

  rule '_._((V:Val, .Vals),, popBack(.Vals)) => .Vals [anywhere]
  rule '_`,_((V:Val, Vl:Vals),, popBack(.Vals))
       => 
       '_._(V,, '_._(Vl:Vals,, popBack(.Vals)))
       [anywhere]

/*@
Push back:\\
$v_0,\ldots,\texttt{pushBack}((v_i,\ldots),v)\Rightarrow v_0,\ldots,v_i,\texttt{pushBack}((v_{i{+}1},\ldots),v)$\\
$v_0,\ldots,v_{n{-}1}\texttt{pushBack}(\texttt{.Vals},v)\Rightarrow v_0,\ldots,v_{n{-}1}, v$\\
Time complexity: $O(size(L))$
*/

  rule '_._(.Vals,, pushBack(X:Val)) => (X, .Vals) [anywhere]
  rule '_._((V:Val, Vl:Vals),, pushBack(X:Val))
       => 
        '_`,_(V,, '_._(Vl:Vals,, pushBack(X)))
      [anywhere]

/*@
Lookup:\\
$\texttt{lookup}((v_j,\ldots),i)\Rightarrow \texttt{lookup}((v_{j{+}1},\ldots),i{-}1)$\\
$\texttt{lookup}((v_{i},\ldots),0)\Rightarrow v_{i}$\\
Time complexity: $O(i)$
*/

/*
  rule lookup((V:Val, Vl:Vals), 0) => V
  rule lookup((V:Val, Vl:Vals), I:Int)
       => 
       lookup(Vl:Vals, I -Int 1)
       when I >Int 0
*/

/*@
Update:\\
$v_0,\ldots,\texttt{update}((v_j,\ldots),i,v)\Rightarrow v_0,\ldots,v_i,\texttt{update}((v_{i{+}1},\ldots),i{-}1,v)$ if $i>0$\\
$v_0,\ldots,v_i\texttt{update}((v_{i{+}1},\texttt{.Vals}), 0, v)\Rightarrow v_0,\ldots,v_i, v, v_{i{+}1},\ldots,v_{n{-}1}$\\
Time complexity: $O(size(L))$
*/

  rule '_._((V:Val, Vl:Vals),, update(0, V':Val)) => (V', Vl) [anywhere]
  rule '_._((V:Val, Vl:Vals),, update(I:Int, V':Val))
       => 
       (V, '_._(Vl:Vals,, update(I -Int 1, V')))
       when I >Int 0
       [anywhere]


//@ \subsection{Operations on structures and arrays}

  //@ Lookup:

  syntax Val ::= "lookup" "(" Vals "," Exp ")" [function]
               | "update" "(" Vals "," Exp "," Val ")" [function]

  rule lookup({_ X |-> V:Val _}, X:Name) => V

  rule lookup({_ X |-> V:Val _}, X:Name[I:Int]) => lookup(V, I)

  rule lookup({_ X |-> V:Val _}, '_._(X:Name,, E:Exp)) => lookup(V, E)

  rule lookup({_ X |-> V:Val _}, '_._(X:Name[I:Int],, E:Exp)) => lookup(lookup(V, I), E)

  rule lookup({_ I |-> V:Val _}, I:Int) => V


  //@ Update:

  rule update({ M:Map }, X:Name, V:Val) => { M[V/X] } 

  rule update({ M:Map }, I:Int, V:Val) => { M[V/I] } 

  rule update({M:Map X |-> V':Val}, '_._(X:Name,, E:Exp), V:Val)
       =>
       {M (X |-> (update(V', E, V)))}  

  rule update({M:Map X |-> V:Val}, X:Name[I:Int], V':Val) => { M (X |-> (update(V, I, V'))) }
 
  rule update({M:Map X |-> V':Val}, '_._(X:Name[I:Int],, E:Exp), V:Val)
       =>
       {M (X |-> (update(V', I, (update(lookup(V', I), E, V)))))}


  //@ Auxiliary functions
  syntax Bool ::= "isFieldName" "(" Exp ")" [function]
  rule isFieldName(X:Name) => true
  rule isFieldName('_`[_`](_:Name,, _:Exp)) => true
  rule isFieldName('_._(_:Name,, E:Exp)) => isFieldName(E)
  rule isFieldName('_._('_`[_`](_:Name,, _:Exp),, E:Exp)) => isFieldName(E)

  // the following function is used to update the global and local states
  syntax Map ::= "mergeMap" "(" Map "," Map "," Map ")" [function]
  rule mergeMap(L:Map, _:Map, .Map) => L
  rule mergeMap((L:Map X:Name |-> V:Val), (R:Map X |-> V':Val), (J:Map X |-> _:Val))
       =>
       mergeMap((L X |-> V'), R, J)

endmodule