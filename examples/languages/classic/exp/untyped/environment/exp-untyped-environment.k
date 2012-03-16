
module EXP-UNTYPED-ENVIRONMENT-SYNTAX

/*@ \section{Syntax}
Unlike in the substitution-based definition, in this environment-based
definition of EXP we can defer the definition of the syntactic
subcategory of values to the semantics.  Since identifiers are not
values anymore, we do not need to restrict the semantics of equality
testing to redex positions anymore. */

/*@ \subsection{Arithmetic constructs}
These are identical to those in imperative and object oriented
languages, for example see IMP, IMPP, SIMPLE, KOOL\@. */

  syntax Exp ::= #Int | #Bool | #Id
               | Exp "+" Exp                [:strict prec 33 gather(E e):]
               | Exp "-" Exp                [:strict prec 33 gather(E e):]
               | Exp "*" Exp                [:strict prec 31 gather(E e):]
               | Exp "/" Exp                [:strict prec 31 gather(E e):]
               | Exp "%" Exp                [:strict prec 31 gather(E e):]
               | "-" Exp                    [:strict:]
               | Exp "<" Exp                [:strict prec 37:]
               | Exp "<=" Exp               [:strict prec 37:]
               | Exp ">" Exp                [:strict prec 37:]
               | Exp ">=" Exp               [:strict prec 37:]
               | Exp "==" Exp               [:strict prec 37:]
               | Exp "!=" Exp               [:strict prec 37:]
               | Exp "and" Exp              [:strict prec 55 gather(E e):]
               | Exp "or" Exp               [:strict prec 59 gather(E e):]
               | "not" Exp                  [:strict prec 53:]

/*@ \subsection{Functional constructs}
Unlike in the substitution-based definition, \texttt{lambda} is now an
expression rather than a value construct.  As seen in the semantics,
$\lambda$-abstractions will evaluate to closures.  We desugar
\texttt{let} and \texttt{letrec} the same way as in the
substitution-based definition. */

  syntax Exp ::= "if" Exp "then" Exp "else" Exp [:strict(1):]
               | "lambda" #Id "." Exp       [:latex "\lambda{#1}.{#2}":]
               | Exp Exp                    [:strict prec 10 gather(E e):]
               | "mu" #Id "." Exp           [:latex "\mu{#1}.{#2}":]
               | "let" #Id "=" Exp "in" Exp
               | "letrec" #Id #Id "=" Exp in Exp

  macro let X:#Id = E:Exp in E':Exp = (lambda X . E') E
  macro (letrec F:#Id X = E in E') = (let F = mu F . (lambda X . E) in E')

end module


module EXP-UNTYPED-ENVIRONMENT
  imports EXP-UNTYPED-ENVIRONMENT-SYNTAX

/*@ \section{Semantics}
The EXP semantics below is environment-based, so \texttt{lambda} and
\texttt{mu} abstractions evaluate to closures. */

/*@ \subsection{Values and results}
We start with primitive values here, and add closures later.  Like in
IMP, we prefer to define values as a distinguished subsyntactic
category of \textit{Exp}, as opposed to defining them directly as \K
results. */

  syntax Val ::= #Int | #Bool
  syntax Exp ::= Val
  syntax KResult ::= Val

/*@ \subsection{Configuration}
The configuration below is standard for trivial environment-based
semantics.  For example, it is identical to that of IMP\@. */

  configuration <T color="yellow" multiplicity="?">
                  <k color="green"> $PGM:Exp </k>
                     <env color="LightSkyBlue"> .Map </env>
                     <store color="white"> .Map </store>
                     <nextLoc color="gray"> 0 </nextLoc>
                </T>
				<result multiplicity="?"> .K </result>
  
  // termination rule; useful for making sure program finished.  
  // Can be removed when we have better krun tools for displaying final config
  rule <T>... <k> V:Val </k> ...</T> => <result> V </result>


/*@ \subsection{Arithmetic constructs}
The rules below are taken over, unchanged, from the semantics of IMP\@. */

  rule <k> X:#Id => E:Exp ...</k>
       <env>... X |-> L:#Nat ...</env>
       <store>... L |-> E ...</store>
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

/*@ \subsection{Conditional}
The two rules below are straightforward, almost identical to those in
IMP\@.  The only difference is that in EXP the conditional is an
expression, rather than a statement, construct. */

  rule if  true then E else  _  => E
  rule if false then  _  else E => E

/*@ \subsection{$\lambda$-abstraction and application}
$\lambda$-abstractions evaluate to {\em closures} (first rule below),
which hold the environment in which the $\lambda$-abstraction was
declared.  This way, at application time (second rule below), the
environment provides bindings for the variables which appear free in
the body of the $\lambda$-abstraction.  The environment needs to be
properly recovered after the application of the closure, which is
achieved by putting the ``marker'' \texttt{env} in the computation,
which holds the environment to which we should switch after the
closure application yields a value (the third rule below).  We use the
same technique in all our environment-based \K language definitions.
Note the fourth rule below.  This structural rule is theoretically
unnecessary, but it can make a big difference in performance.  It
achieves the same beneficial effects as tail recursion.  The idea
here is that we do not want to grow the computation (stack)
indefinitely when we have tail-recursive programs.  Since
tail-recursion leads to consecutive environment-recovery operations,
the fourth rule below ensures that only the last environment-recovery
operation is kept in the computation, so the computation will not grow
when programs are in a tail recursive form. */

  syntax Val ::= "closure-lambda" "(" Map "," #Id "," Exp ")"
                   [:latex "\textsf{closure}_\lambda({#1},{#2},{#3})":]
  rule <k> lambda X . E => closure-lambda(Rho:Map,X,E) ...</k>
       <env> Rho </env>
  rule <k> closure-lambda(Rho,X,E) V:Val => E ~> env(Rho') ...</k>
       <env> Rho':Map =>  Rho[L/X] </env>
       <store_> . => L|->V <_/store>
       <nextLoc> L => L +Nat 1 </nextLoc>

  syntax K ::= "env" "(" Map ")"
  rule <k> V ~> (env(Rho) => .) ...</k> <env> _ => Rho </env>  [:structural:]
  rule (env(_) => .) ~> env(_)                                 [:structural:]


/*@ \subsection{Recursion abstraction}
The $\mu$-abstraction needs its own closure.  It may look like all
you need to do is to store the $\mu$-abstraction at some location,
without any closure, bind its variable to that location and then
evaluate its body, but that does {\em not} work.  Consider, for
example, the following EXP program:
\begin{quote}
\begin{verbatim}
  let y = 0
  in letrec f x = if x == 0 then y else let y = 1
                                        in f(x - 1)
     in f 1
\end{verbatim}
\end{quote}
Without a $\mu$-closure, the \texttt{letrec}-free \texttt{y} in the
\texttt{then} branch of the conditional will be captured by the
\texttt{let}-bound \texttt{y} in the \texttt{else} branch of the
conditional. */

  syntax Exp ::= "closure-mu" "(" Map "," Exp ")"
                   [:latex "\textsf{closure}_\mu({#1},{#2})":]
  rule <k> mu X . E => closure-mu(Rho[L/X],E) ...</k>
       <env> Rho </env>
       <store>... . => L |-> closure-mu(Rho[L/X],E) ...</store>
       <nextLoc> L => sNat L </nextLoc>
  rule <k> closure-mu(Rho,E) => E ~> env(Rho') ...</k>
       <env> Rho' => Rho </env>

***(
// we really need mu closures ...
// the rule below is wrong, because the free variables
// of E can be captured
  rule <k> mu X . E => E ~> env(Rho) ...</k>
       <env> Rho => Rho[L/X] </env>
       <store_> . => L |-> mu X . E <_/store>
       <nextLoc> L => L +Nat 1 </nextLoc> 
***)

end module
