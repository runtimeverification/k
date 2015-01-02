// Copyright (c) 2013-2015 K Team. All Rights Reserved.

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

  //@ Boolean Expressions

  syntax BExp ::= Bool
                | IExp "=" IExp [strict]
                | "!" BExp [strict]
                | BExp "&" BExp [strict(1)]

  //@ Integer Expressions
  syntax IExp ::=  Int | Id
                | "hd" "(" SExp ")" [strict]
                | "(" IExp ")" [brackets]
                > Id "(" IExps ")" [strict(2)]
                > Id "." IExp [strict(2)]
                > IExp "<|" BExp "|>" IExp [strict(2)]
                | IExp "+" IExp [strict]

  syntax IExps ::= List{IExp,","} [strict]
  //@ Stream Expressions


  syntax SExp ::= Id
                | "tl" "(" SExp ")" [strict, prefer]
//                | "(" SExp ")" [brackets]
                > Id "(" SExps ")" [strict(2)]
                > Id "." SExp [lsexp]
                > IExp ":" SExp [strict(1), right, constr]
                | "[]"
  syntax SExps ::= List{SExp,","} [strict]


  //@ Expressions
  syntax Exp ::= IExp | SExp
  syntax Exps ::= List{Exp,","} [strict]

  //@ Stream Specifications
  syntax SSpec ::= Id ":~" SExp ";"
                 | Id "(" Ids ")" ":~" SExp ";"
                 | Id ":=" IExp ";"
                 | Id "(" Ids ")" ":=" IExp ";"
  syntax Ids ::= List{Id,","}
  syntax SSpecs ::= SSpec | SSpec SSpecs [right]

/*@ A program is a sequence of specification followed by an
  expression to be evaluated. If the expression is a stream one, then
  the evaluation is a infinite process and therefore the debugger should
  be used for such cases.
*/
  syntax SPgm ::= SSpecs Exp


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
  syntax KItem ::= "lambda" "(" Ids ")" Exp

/*@ The result values are integers and stream expression for that at  least
  the head is evaluated to an integer:
*/

  syntax KResult ::= Int | Bool


  rule isKResult(_:Int : _:SExp) => true


  //@ Preprocessing

  rule SS:SSpec SSs:SSpecs E:Exp => SS ~> SSs E

  rule (SS:SSpec E:Exp) => SS ~> E

  rule <k> F:Id :~ SE:SExp; => . ...</k>
       <sspecs>... . => F |-> lambda(.Ids) SE </sspecs>

  rule <k> F:Id(Ys:Ids) :~ SE:SExp; => . ...</k>
       <sspecs>... . => F |-> lambda(Ys) SE </sspecs>

  rule <k> F:Id := IE:IExp; => . ...</k>
       <sspecs>... . => F |-> lambda(.Ids) IE </sspecs>

  rule <k> F:Id(Ys:Ids) := IE:IExp; => . ...</k>
       <sspecs>... . => F |-> lambda(Ys) IE </sspecs>

 //@ Computations:

  rule I1:Int = I2:Int => I1 ==Int I2

  rule ! B:Bool => notBool B

  rule true & BE:BExp => BE

  rule false & _:BExp => false

  rule IE:IExp <| true |> _:IExp => IE

  rule _:IExp <| false |> IE:IExp => IE


 //@ The evaluation of the head:

  rule hd(I:Int : _) => I [anywhere]

  //@ The evaluation of tail:

  rule tl(_:Int : SE:SExp) => SE [anywhere]

  //@ When the head is completely evaluated is moved in the cell out:
  rule <k> I:Int => . </k>
       <out> SE:SExp => append(I, SE) </out>
/*
  // this rule exhibith the infinite evaluation process and it
  // is useful for equivalence (see prog-equiv/streams/
  rule <k> I:Int : SE:SExp => SE </k>
       <out> OUT:SExp => append(I, OUT) </out>
*/
  rule <k> I:Int : SE:SExp => . </k>
       <out> OUT:SExp => replace([], I : SE, OUT)  </out>

 //@ Stream specification without parameters:

  rule <k> F:Id => SE ...</k>
       <sspecs>... F |-> lambda(.Ids) SE ...</sspecs>
       [transition]

 //@ Stream specification with parameters:

  rule <k> F:Id(SEs:SExps) => SE[SEs / Xs] ...</k>
       <sspecs>... F |-> lambda(Xs:Ids) SE:SExp ...</sspecs>
       [transition]

  rule <k> F:Id(IEs:IExps) => IE[IEs / Xs] ...</k>
       <sspecs>... F |-> lambda(Xs:Ids) IE:IExp ...</sspecs>
       [transition]


  //@ \section{Auxiliary Operations}

  //@ Substitution

  syntax Exp ::= Exp "[" Exps "/" Ids "]" [function]

  rule SE:Exp[(V:SExp, (V':Exp, Vs:Exps)) / (X:Id, (X':Id, Xs:Ids))]
       =>
      (replace(X, V, SE))[(V', Vs) / (X', Xs)]

  rule SE:Exp[(V:Exp, .Exps) / (X:Id, .Ids)] => replace(X, V, SE)


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
