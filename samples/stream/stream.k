/*!
\setlength{\parindent}{1em}
\title{CinK -- an experiment on how to think in \K}
\author{Dorel Lucanu (\texttt{dlucanu@info.uaic.ro})}
\organization{Alexandru Ioan Cuza University of Ia\c{s}i, Romania}
\newcommand{\myparagraph}[1]{\textbf{#1}}
\newcommand{\KTool}{\K tool\xspace}
\newcommand{\Cink}{CinK\xspace}
\newcommand{\STREAM}{\textsc{stream}\xspace}


  \section{Introduction}
  \STREAM a very simple language able to handle corecursive programs over
  integer streams (= infinite sequence of integers).
  The standard semantics for corecursive semantics is based on lazy evaluation,
  which delays the evaluation of an expression until its value is needed.
  Obviously, the evaluation of such expressions requires only a finite part
  of the infinite data structure. For the case of streams, this is usually given
  by a finite number of elements lying at the beginning of  the stream.
  Therefore we consider that a stream expression is in a \emph{result} form
  if is of the form $i\terminal{:} \mathit{SE}$, where the integer $i$ is 
  the first element of the stream. Beside the constructor
  $\_\!\terminal{:}\!\_$, two functions, often called destructors,
  are essential in handling streams:  $\terminal{hd}(xs)$, which returns 
  the first element of the stream, and 
  $\terminal{tl(}\mathit{xs}\terminal{)}$, which returns the stream obtained
  after the first element is removed.
*/

module STREAM 

  //@ Integer Expressions
  syntax IExp ::=  Int
                | "hd" "(" SExp ")" [strict, context(svalue)]

  //@ Stream Expressions
  syntax SExp ::= Id
                | "tl" "(" SExp ")" [strict, context(svalue), prefer]
                > Id "(" SExps ")" [strict(2), context(svalue)]
                > IExp ":" SExp [right]
                | "[]"
  syntax SExps ::= List{SExp,","} [strict, context(svalue)]

  //@ Expressions
  syntax Exp ::= IExp | SExp

  //@ Stream Specifications
  syntax SSpec ::= Id ":=" SExp ";"
                 | Id "(" Ids ")" ":=" SExp ";"
  syntax Ids ::= List{Id,","}
  syntax SSpecs ::= SSpec | SSpec SSpecs [right]

/*@ A program is a sequence of specification followed by an 
  expression to be evaluated. If the expression is a stream one, then
  the evaluation is a infinite process and therefore the debugger should
  be used for such cases.
*/
  syntax SPgm ::= SSpecs Exp 


//@ Contexts
  syntax K ::= svalue(K) [klabel(svalue)]
/*@
  We have to specify which arguments of the svalu context are strict:
*/

  context svalue(hd(HOLE => svalue(HOLE)))  // a head argument
  context svalue(tl(HOLE => svalue(HOLE)))  // a tail argument
  context svalue((HOLE => svalue(HOLE)) : _) // the constructor: 1st case
  context svalue((HOLE => svalue(HOLE)), _:SExps) // the constructor: 2nd case
  context svalue(_:SExp, (HOLE => svalue(HOLE)))  // expression list: 1st case
  context svalue((HOLE => svalue(HOLE)), .SExps)  // expression list: 2nd case

  //@ Configuration

/*@
  Besides the cell k, there two additional cells.
  The cell \tetxtsf{specs} stores the the definition of the corecursive functions. 
  The cel \textsf{out} is used to exhibit the partial evaluation of the streams:
  each time a result stream expression is at the top of the computation
  (i.e., at the beginning of the k cell), the first element is moved to 
  the output cell. This cell is essential for the stream equivalence.
*/
  configuration 
    <k> $PGM:SPgm </k>
    <sspecs> .Map </sspecs>
    <out> [] </out> 

 //@ The right-hand side of a specification is stored as a $\lambda$-expression:
  syntax K ::= "lambda" "(" Ids ")" SExp

/*@ The result values are integers and stream expression for that at  least
  the head is evaluated to an integer:
*/
  syntax KResult ::= Int 

  rule isKResult(_:Int : _:SExp) => true

  //@ Preprocessing

  rule SS:SSpec SSs:SSpecs E:Exp => SS ~> SSs E

  rule (SS:SSpec E:Exp) => SS ~> E

  rule <k> F:Id := SE:SExp; => . ...</k>
       <sspecs>... . => F |-> lambda(.Ids) SE </sspecs>

  rule <k> F:Id(Ys:Ids) := SE:SExp; => . ...</k>
       <sspecs>... . => F |-> lambda(Ys) SE </sspecs>

  //@ Computations:
  rule IE:IExp : SE':SExp => IE ~> SE'

 //@ The evaluation of the head:
  rule svalue(hd(I:Int : _) => I)

  rule hd(I:Int : _) => I

  //@ The evaluation of tail:
  rule svalue(tl(_:Int : SE:SExp) => SE)

  rule tl(_:Int : SE:SExp) => SE
  
  //@ When the head is completely evaluated is move in the cell out:
  rule <k> I:Int => . ...</k>
       <out> SE:SExp => append(I, SE) </out>

 //@ Stream specification without parameters:
  rule <k> svalue(F:Id => SE) ...</k>
       <sspecs>... F |-> lambda(.Ids) SE:SExp ...</sspecs>

  rule <k> F:Id => SE ...</k>
       <sspecs>... F |-> lambda(.Ids) SE:SExp ...</sspecs>
       [transition]

 //@ Stream specification with parameters:
  rule <k> svalue(F:Id(SEs:SExps) => SE[SEs / Xs]) ...</k>
       <sspecs>... F |-> lambda(Xs:Ids) SE:SExp ...</sspecs>

  rule <k> F:Id(SEs:SExps) => SE[SEs / Xs] ...</k>
       <sspecs>... F |-> lambda(Xs:Ids) SE:SExp ...</sspecs>
       [transition]

  //@ \section{Auxiliary Operations}

  //@ Substitution

  syntax SExp ::= SExp "[" SExps "/" Ids "]" [function]

  rule SE:SExp[(V:SExp, (V':SExp, Vs:SExps)) / (X:Id, (X':Id, Xs:Ids))] => (replace(X, V, SE))[(V', Vs) / (X', Xs)]

  rule SE:SExp[(V:SExp, .SExps) / (X:Id, .Ids)] => replace(X, V, SE)


  //@ Append

  syntax SExp ::= append(Int, SExp) [function]

  rule append(I:Int, []) => I : []
  rule append(I:Int, (J:Int : SE)) => J : append(I, SE)

  //@ Replace X:K by V:K in E:K

  syntax K ::= replace(K,K,K) [function]
  syntax KList ::= replaceList(K,K,KList) [function]
  syntax KList ::= replaceListList(KList,K,KList) [function]

  rule replace(X:K, V:K, X) => V
  rule replace(XL:KLabel(XKL:KList), V:K, EL:KLabel(EKL:KList)) => EL(replaceList(XL(XKL), V, EKL))  when XL =/=KLabel EL
  rule replace(XL:KLabel(XKL:KList), V:K, XL:KLabel(EKL:KList)) => XL(replaceListList(XKL, V, EKL))

  rule replaceList(X:K, V:K, .KList) => .KList
  rule replaceList(X:K, V:K, (E:K,, EKL:KList)) => replace(X, V, E),, replaceList(X, V, EKL)

  rule replaceListList(.KList, V:K, EKL:KList) => EKL
  rule replaceListList((X:K,, XKL:KList), V:K, (E:K,, EKL:KList)) => replace(X, V, E),, replaceListList(XKL, V, EKL)

endmodule
