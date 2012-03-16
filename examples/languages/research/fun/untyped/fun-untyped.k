
module FUN-UNTYPED-SYNTAX
/*@ \section{Syntax}
FUN is an expression language.  The constructs below are split into
several categories, for clarity: arithmetic constructs, conventional
functional constructs, lists, references, and
call-with-current-continuation (callcc).  */

/*@ \subsection{Arithmetic constructs}
The constructs below are standard; they are present in almost all our
\K language definitions. */

  syntax Exp ::= #Int | #Bool | #String | #Id
               | Exp "+" Exp           [:strict prec(33) gather(E e):]
               | Exp "-" Exp           [:strict prec(33) gather(E e):]
               | Exp "*" Exp           [:strict prec(31) gather(E e):]
               | Exp "/" Exp           [:strict prec(31) gather(E e):]
               | Exp "%" Exp           [:strict prec(31) gather(E e):]
               | "-" Exp               [:strict:]
               | Exp "<" Exp           [:strict prec(37):]
               | Exp "<=" Exp          [:strict prec(37):]
               | Exp ">" Exp           [:strict prec(37):]
               | Exp ">=" Exp          [:strict prec(37):]
               | Exp "==" Exp          [:strict prec(37):]
               | Exp "!=" Exp          [:strict prec(37):]
               | Exp "and" Exp         [:strict prec(55) gather(E e):]
               | Exp "or" Exp          [:strict prec(59) gather(E e):]
               | "not" Exp             [:strict prec(53):]

/*@ \subsection{Functional constructs}
The following constructs are like those of EXP, but slightly more
complex.  Recall that the syntax that we define in \K is not meant to
serve as a ultimate parser for the defined language, but rather as a
convenient notation for \K abstract syntax trees, which we prefer when
we write the semantic rules.  Thus, like in other languages, we take
the freedom to define the syntax in ways which are convenient both in
terms of parsing a reasonable number of programs without a need for an
external parser, and in terms of elegance for the semantic rules.
Parsing precisely the desired programs or giving good parsing error
messages have a lower priority.  In our case here, note that we want
to be able to parse functions of the form
``\texttt{fun (a,b) (x,y) -> a(x,y) + b(x,y)}''
and similarly for bindings, that is, 
``\texttt{let f (a,b) (x,y) = a(x,y) + b(x,y) in ...}''.

One way to parse such expressions is to define a more ``generous''
syntax, like we do below.  More precisely, we allow \texttt{fun} to
take any list of expressions as first argument (first production),
making sure that application is extended to allow any list of
expressions to be applied to any list of expressions.  Of course, this
syntactic relaxation permits many wrong programs to be parsed, but
that is not a problem because we are not going to give semantics to
wrong combinations, so those programs will get stuck; moreover, our
type inferencer will reject those programs anyway.  In an ideal world,
we would define a new syntactic category of space-separated
parenthesis-enclosed identifier lists, say \textit{Parameters}, and
then have \texttt{fun} take \textit{Parameters} as its first argument.
Unfortunately, the current \K tool eventually collapses all the
syntactic categories into one, $K$, and thus the space-separated
parameters get in parsing conflict with function application.  It is
highly recommended in the current version of the \K tool to avoid
defining syntactic constructs which have the same signature when
non-terminals are collapsed.  If you are willing to change the
parameter separator from space into something else, say
``\texttt{:}'', then you can define a more precise syntax but your
programs will look uglier, e.g.,
``\texttt{fun (a,b):(x,y) -> a(x,y) + b(x,y)}'', etc.

Similarly, we allow \texttt{let} and \texttt{letrec} to take any
expression in place of its binding and define the ``\texttt{=}''
binder as an expression construct.  This allows us to use the already
existing Boolean conjunction construct, \texttt{and}, to create larger
bindings, e.g., like in ``\texttt{let x = 7 and y = 5 in ...}''.
Again, semantics will be given only to the correct programs.
Moreover, the \texttt{and} used to create binders will never be
evaluated as a the Boolean arithmetic construct, as evaluation
permission will never be given to the first argument of \texttt{let}
or \texttt{letrec}.  Some desugaring macros curry function 
declarations and group bindings, so that the semantics only needs to
consider the cases where function declarations have the form
``\texttt{fun (x1,...,xn) -> e}'' and where let-bindings have the form
``\texttt{let (x1,...,xn) = (e1,...,en) in e}''
(and similarly for \texttt{letrec}). */

  syntax Exp ::= "fun" Exps "->" Exp
               | Exps Exps             [:strict prec(10) gather(E e):]
               | Exps "=" Exps         [:prec(53):]   --- Bindings
               | "let" Exp "in" Exp
               | "letrec" Exp "in" Exp
               | "if" Exp
                 "then" Exp
                 "else" Exp            [:strict(1):]
  syntax Exps ::= List{Exp,","}
  syntax Ids  ::= List{#Id,","}
  macro fun Es1:Exps Es2:Exps -> E:Exp = fun Es1 -> fun Es2 -> E
  macro (E1:Exp Es:Exps = E) = (E1 = fun Es -> E)
  macro (X:#Id = E:Exp) and (Xs:Ids = Es:Exps) = ((X,Xs) = (E,Es))

/*@ We want to allow the syntax \texttt{()} for the empty list of
expressions/identifiers in FUN programs, so we also add it to the
syntax together with a desugaring macro: */

  syntax Exps ::= "(" ")"
  macro () = .Exps

/*@ \subsection{Lists}
FUN lists are formed by enclosing comma-separated lists of
expressions (i.e., terms of sort \textit{Exps}) in square brackets.
We use the conventional Lisp/Scheme terminology for the list
constructs: \texttt{car} extracts the first element of the list if the
list has at least one element (and gets stuck otherwise), \texttt{cdr}
evaluates to the rest of the list except the first element and fails
if the list is empty, \texttt{null?} checks whether the list is empty,
and \texttt{cons} is the dual of \texttt{car} and \texttt{cdr}
together, that is, it places an element in from of a list. */

  syntax Exp ::= "[" Exps "]"          [:strict hybrid prec(0):]
               | "car" Exp             [:strict prec(0):]
               | "cdr" Exp             [:strict prec(0):]
               | "null?" Exp           [:strict prec(0):]
               | "cons" Exp Exp        [:strict:]

/*@ \subsection{References}
The construct \texttt{ref} takes an expression, evaluates it and
returns a reference to where that value is stored.  This way,
references become first class values in FUN.  The construct
\texttt{\&} also evaluates to a reference, but one where the
variable passed as argument stores its value.  The construct
\texttt{*} takes a reference and evaluates to the value stored there.
The construct \texttt{:=} takes two expressions, the first expected to
evaluate to a reference; the value of its second argument will be
stored at the location to which the first points (the old value is
thus lost).  Finally, since expression evaluation now has side
effects, it makes sense to also add a sequential composition
construct, which is sequentially strict.  This evaluates to the value
of its second argument; the value of the first argument is lost (which
has therefore been evaluated only for its side effects. */

  syntax Exp ::= "ref" Exp             [:strict:]
               | "&" #Id               [:prec(0):]
               | "*" Exp               [:strict:]
               | Exp ":=" Exp          [:strict:]
               | Exp ";" Exp           [:seqstrict prec(110) gather(e E):]

/*@ \subsection{Call-with-current-continuation}
Call-with-current-continuation, named \texttt{callcc} in FUN, is a
powerful control operator that originated in the Scheme programming
language, but it now exists in many other functional languages.  It
works by evaluating its argument, expected to evaluate to a function,
and passing the current continuation, or evaluation context (or
computation, in \K terminology), as a special value to it.  When/If
this special value is invoked, the current context is discarded and
replaced with the one held by the special value and the computation
continues from there.  It is like taking a snapshot of the execution
context at some moment in time and then, when desired, being able to
get back in time to that point.  If you like games, it is like saving
the game now (so you can work on your homework!) and then continuing
the game tomorrow or whenever you wish. */

  syntax Exp ::= "callcc" Exp          [:strict:]

/*@ To highlight the power of callcc, we include exceptions in FUN by
simply desugaring them to callcc using a macro. */

  syntax Exp ::= "try" Exp "catch" "(" #Id ")" Exp
  syntax #Id ::= "$continuation" | "$value" | "throw"

--- assume that continuation and value are not free in E and E'
  macro try E catch(X:#Id) E':Exp
      = callcc (fun $continuation
                -> (fun throw -> E:Exp)
                     (fun $value -> $continuation ((fun X -> E') $value)))

end module


module FUN-UNTYPED
  imports FUN-UNTYPED-SYNTAX

/*@ \section{Semantics}
The semantics below is environment-based.  See the EXP language for an
example of a substitution-based definition of a simpler functional
language and AGENT for a more complex one.
We preferred an environment-based definition here for two reasons:
first, FUN has the variable address construct \texttt{\&x}, which
grabs the reference of variable \texttt{x}, and this is easier to
define in an environment-based style; and second, environment-based
definitions tend to be more efficient when executed in \K\@. */

/*@ \subsection{Values and results}
We only define integers and Booleans as values here, but will add more
values later.  We only discuss the features whose semantics is not
identical to that in EXP or IMP\@. */

  syntax Val ::= #Int | #Bool
  syntax Vals ::= List{Val,","}
  syntax Exp ::= Val
  syntax KResult ::= Val

//@ \subsection{Configuration}

  configuration <T multiplicity="?">  <k color="green"> $PGM:Exp </k>
                     <env color="violet"> .Map </env>
                     <store color="white"> .Map </store>
                     <nextLoc color="gray"> 0 </nextLoc>
                </T>
				<result multiplicity="?"> .K </result>

  // termination rule; useful for making sure program finished.  
  // Can be removed when we have better krun tools for displaying final config
  rule <T>... <k> V:Val </k> ...</T> => <result> V </result>


//@ \subsection{Lookup}

  rule <k> X:#Id => V:Val ...</k>
       <env>... X |-> L:#Nat ...</env>
       <store>... L |-> V ...</store>

//@ \subsection{Arithmetic expressions}

  rule I1:#Int + I2:#Int => I1 +Int I2
  rule _-_(I1,I2) => _-Int_(I1,I2)
  rule I1 * I2 => I1 *Int I2
  rule I1 / I2 => I1 /Int I2 when I2 =/=Bool 0
  rule I1 % I2 => I1 %Int I2 when I2 =/=Bool 0
  rule - I:#Int => -Int I
  rule I1 < I2 => I1 <Int I2
  rule I1 <= I2 => I1 <=Int I2
  rule I1 > I2 => I1 >Int I2
  rule I1 >= I2 => I1 >=Int I2
  rule V1:Val == V2:Val => V1 ==Bool V2
  rule V1 != V2 => V1 =/=Bool V2
  rule T1:#Bool and T2:#Bool => T1 andBool T2
  rule T1 or T2 => T1 orBool T2
  rule not(T:#Bool) => notBool(T)

/*@ \subsection{Functions and Closures}
The semantics of function and application below follow the same
closure-based idea like in the environment-based semantics of EXP,
although for clarity we prefer to make use of a \texttt{bindTo}
construct like in the semantics of SIMPLE and KOOL\@. */

  syntax Val ::= "closure" "(" Map "," Ids "," Exp ")"
  rule <k> fun Xs:Ids -> E:Exp => closure(Rho:Map,Xs,E) ...</k>
       <env> Rho </env>
  rule <k> closure(Rho,Xs,E) Vs:Vals
        => bindTo(Xs,Vs) ~> E ~> env(Rho') ...</k>
       <env> Rho':Map => Rho </env>

/*@ \subsection{Let and Letrec}
To highlight the difference between \texttt{let} and
\texttt{letrec}, we prefer to give them direct semantics instead of
desugaring them like in EXP.  See the formal definitions of
\texttt{bindTo}, \texttt{bind}, and
\texttt{assignTo} at the end of this module.  Informally, 
\texttt{bindTo($\it Xs$,$\it Es$)} first evaluates the expressions
${\it Es}\in\textit{Exps}$ in the current environment (i.e., it is
strict in its second argument), then it binds the variables in
${\it Xs}\in\textit{Ids}$ to new locations and adds those bindings
to the environment, and finally writes the values previously obtained
after evaluating the expressions $\it Es$ to those new locations;
\texttt{bind($\it Xs$)} does only the bindings of
$\it Xs$ to new locations and adds those bindings to the
environment; and \texttt{assignTo($\it Xs$,$\it Es$)} evaluates
the expressions $\it Es$ in the current environment and then it
writes the resulting values to the locations to which the variables
$\it Xs$ are already bound to in the environment.

Therefore, ``\texttt{let $\it Xs$=$\it Es$'' in $\it E$} first
evaluates $\it Es$ in the current environment, then adds new
bindings for $\it Xs$ to fresh locations in the environment, then
writes the values of $\it Es$ to those locations, and finally
evaluates \textit{E} in the new environment, making sure that the
environment is properly recovered after the evaluation of \textit{E}.
On the other hand, \texttt{letrec} does the same things but in a
different order: it first adds new bindings for $\it Xs$ to fresh
locations in the environment, then it evaluates $\it Es$ in the new
environment, then it writes the resulting values to their
corresponding locations, and finally it evaluates \textit{E} and
recovers the environment.  The crucial difference is that the
expressions $\it Es$ now see the locations of the variables
$\it Xs$ in the environment, so if they are functions, which is
typically the case with \texttt{letrec}, their closures will
encapsulate in their environments the bindings of all the bound
variables, including themselves (thus, we may have a closure value
stored at location \textit{L}, whose environment contains a binding of
the form $\textit{F} \mapsto \textit{L}$; this way, the closure can
invoke itself). */

  rule <k> let Xs = Es:Exps in E
        => bindTo(Xs,Es) ~> E ~> env(Rho) ...</k>
       <env> Rho </env>

  rule <k> letrec Xs = Es:Exps in E
        => bind(Xs) ~> assignTo(Xs,Es) ~> E ~> env(Rho) ...</k>
       <env> Rho </env>

/*@ \subsection{Callcc}
Call-with-current continuation is quite easy to define in \K.  We
first need to define a special value wrapping an execution context,
that is, an environment saying where the variables should be looked up
and a computation structure saying what is left to execute (in a
substitution-based definition, like that of AGENT, this special value
would be even simpler, as it would only need to wrap the computation
structure).  Then \texttt{callcc} creates such a value containing the
current environment and the current remaining computation, and passes
it to its argument function.  When/If invoked, the special value
replaces the current execution context with its own and continues the
execution normally. */

  syntax Val ::= "cc" "(" Map "," K ")"
  rule <k> (callcc V => V cc(Rho,K)) ~> K </k> <env> Rho </env> 
  rule <k> cc(Rho,K:K) V ~> _ => V ~> K </k> <env> _ => Rho </env> 

//@ \subsection{Conditional}

  rule if  true then E else _ => E
  rule if false then _ else E => E 

/*@ \subsection{Lists}
The semantics of lists below is self-explanatory. */

  rule car [V,_:Vals] => V
  rule cdr [_:Val,Vs] => [Vs]
  rule null? [] => true
  rule null? [_:Val,_:Vals] => false
  rule cons V [Vs] => [V,Vs]

/*@ \subsection{References}
The semantics of references is also self-explanatory, noting that
locations in FUN are nothing but natural numbers.  Thus, the FUN
programmer is allowed to even do arithmetic with references.  To
prevent that, you can make references different from natural numbers,
for example to be terms of the form \texttt{loc($N$)}, where $N$
ranges over natural numbers, and replace the successor operation
currently used to increment the next available location counter with a
special next-location operation that works on locations instead of
natural numbers.  Note that \texttt{\&$X$} grabs the location of $X$
from the environment; this operation would be harder to define in a
substitution-based approach. */

  rule <k> ref V => L ...</k>
       <store>... . => L |-> V ...</store>
       <nextLoc> L => sNat L </nextLoc>
  rule <k> &X => L ...</k> <env>... X|->L ...</env>
  rule <k> *L => V ...</k> <store>... L|->V ...</store>
  rule <k> L:=V => V  ...</k> <store>... L|->(_=>V) ...</store>
  rule V1; V2 => V2


/*@ \subsection{Auxiliary operations}
The environment recovery operation is the same as for EXP and other
languages provided with the \K distribution.  The remaining three
operations have already been explained when we discussed \texttt{let}
and \texttt{letrec} above. */

//@ \subsubsection{Environment recovery}

  syntax K ::= "env" "(" Map ")"
  rule (env(_) => .) ~> env(_)            [:structural:]   --- tail recursion
  rule <k> V ~> (env(Rho) => .) ...</k>
       <env> _ => Rho </env>              [:structural:]

//@ \subsubsection{bindTo and bind}

  syntax K ::= "bindTo" "(" Ids "," Exps ")"        [:strict(2):]
             | "bind" "(" Ids ")"

  rule <k> bindTo(.Ids,.Vals) => . ...</k>             [:structural:]
  rule <k> bindTo((X,Xs => Xs),(V,Vs => Vs)) ...</k>
       <env> Rho => Rho[N/X] </env>
       <store>... . => N |-> V ...</store>
       <nextLoc> N:#Nat => sNat N </nextLoc>              [:structural:]

  rule <k> bind(.Ids) => . ...</k>                      [:structural:]
  rule <k> bind(X,Xs => Xs) ...</k>
       <env> Rho => Rho[N/X] </env>
       <nextLoc> N => sNat N </nextLoc>                   [:structural:]

//@ \subsubsection{assignTo}

  syntax K ::= "assignTo" "(" Ids "," Exps ")"  [:strict(2):]

  rule <k> assignTo(.Ids,.Vals) => . ...</k>            [:structural:]
  rule <k> assignTo((X,Xs => Xs),(V,Vs => Vs)) ...</k>
       <env>... X |-> L ...</env>
       <store>... . => L |-> V ...</store>                [:structural:]

end module
