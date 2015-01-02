// Copyright (c) 2012-2015 K Team. All Rights Reserved.

require "/modules/k-visitor.k"

/*@ \subsection{Code Generation}

Here we show the semantics of the code generation constructs, namely of
\texttt{quote}, \texttt{unquote}, \texttt{lift}, \texttt{eval}.
The interesting aspect of our \K definition of these constructs below is
that it is \textit{language independent}.
That is, nothing needs to change in the semantics below if new syntactic
constructs are added to or removed from Agent.  */

module QUOTE-UNQUOTE-SYNTAX

/*@ \subsubsection{Syntax}

\texttt{lift} and \texttt{eval} are strict, where the former takes the
resulting value and lifts it into a code value, and the later expects its
argument to evaluate to a code value and turns it into its corresponding
code, which is consequently evaluated in the current context.
\texttt{quote} and \texttt{unquote} are not strict.
The former freezes its argument code into a code value, without evaluating
it, except for code appearing as arguments of \texttt{unquote}.
In fact, \texttt{quote} and \texttt{unquote} can be nested; a counter keeps
track of how many times \texttt{quote} appears nested, and only the code
which is unquoted the same number of times gets evaluated in the current
context.
Please refer to languages like Scheme for more details on how these
constructs work.  */

  syntax Exp ::= "quote" Exp    [quote]
               | "unquote" Exp  [unquote]
               | "lift" Exp     [lift, strict]
               | "eval" Exp     [eval, strict]
endmodule

module QUOTE-UNQUOTE
  imports QUOTE-UNQUOTE-SYNTAX
  imports K-VISITOR

/*@ \subsubsection{Semantics}

We here chose to use the generic visitor pre-defined in \K.
A direct definition would be clearer, but although still language-independent
it would involve more rules.
Additionally, this offers an opportunity to illustrate the power of \K's
generic visitors. */

/*@ Define a visitor parametric in a natural number \texttt{N} that applies
\texttt{quoteit} (defined below) with first argument \texttt{N} to \texttt{quote}
and \texttt{unquote} nodes; these nodes are recognized with the predicate
\texttt{isQuote} (also defined below).  We define this visitor as a macro: */

  syntax KItem ::= qVisitor(Int)
  rule qVisitor(N:Int) => #visitor(#label('quoteit),,#klist(N),,
                                   #label('isQuoted),,#klist(.KList))  [macro]

/*@ The \texttt{mQuote} macro defined below simply applies the visitor to a
given K term.  In this particular definition of Agent the K term will always
be an expression, but we want our semantics to be as general as possible, so
we want it to work also if we add other syntactic categories to our language
(e.g., statements):  */

  syntax Exp ::= mQuote(K, Int)
  rule mQuote(E, N) => #visit(E,, qVisitor(N))  [macro]

/*@ The semantics of \texttt{quote E} is defined as follows: visit \texttt{E},
starting with counter 0; whenever a nested \texttt{quote} construct is
encountered, increment the counter and continue; whenever a nested \texttt{unquote}
construct is encountered, if the counter is 0 then execute the unquoted code,
otherwise decrement the counter and continue.
The \texttt{unquote} construct is expected to produce a code value, otherwise
a runtime error will occur if executed (because \texttt{unquote} can only occur
inside the argument expression of a \texttt{quote}).
Since the result of applying a visitor to a K term is the visited K term wrapped
with label \texttt{\#visited}, the semantics of the constructs \texttt{lift}
and \texttt{eval} are defined using the \texttt{\#visited} wrapper: */

  syntax KItem ::= quoteit(Int,K)
  rule quote E => mQuote(E, 0)
  rule quoteit(N, quote E)   => #visiting.kapp(#label('quote_),,mQuote(E, N +Int 1))
  rule quoteit(0, unquote E) => E
  rule quoteit(N, unquote E) => #visiting.kapp(#label('unquote_),,mQuote(E, N -Int 1))
  when (N >Int 0)

  rule lift V:Val => #visited(V)
  rule eval #visited(E:K) => E

/*@ Since we want code values to become actual values in our language, we also
need to explicitly state it that \texttt{\#visited}-wrapped terms belong to
\texttt{Val} (the generic visitor only ensures they are \texttt{KResult}s):  */

  rule isVal(#visited(_)) => true

/*@ Finally, we define the auxiliary predicate testing if a code fragment is a
\texttt{quote} or \texttt{unquote}:  */
  syntax Bool ::= isQuoted(Exp)     [function]
  rule isQuoted(quote E) => true
  rule isQuoted(unquote K) => true
  rule isQuoted(_) => false [owise]

/*@  Conceptually, the above is the conventional definition of
\texttt{quote}/\texttt{unquote}.
However, the definitions that we encountered so far were all language
specific; that is, rules propagating the transformations above through each
particular language construct were given, ending up with a semantics of
\texttt{quote}/\texttt{unquote} as large as the size of the language syntax.
Note that our semantics is fixed and applies to any language.  */
endmodule
