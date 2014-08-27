// Copyright (c) 2012-2014 K Team. All Rights Reserved.

require "builtins/k-equal.k"

/*@ \subsection{Generic Visitors}

\K allows users to define generic visitors, that is, visitors that take any K
term and transform it according to given parameters.
The particular user-defined syntax of the target language is irrelevant for
the visitor, because that is all eventually transformed into K terms, and the
visitors work with the latter.
This is in sharp contrast with conventional visitor-like semantic approaches,
such as those encountered in conventional semantics of
\texttt{quote}/\texttt{unquote} constructs in languages with support for code
generation, which are language-specific, that is, which have a case (semantic rule)
for each language construct.
Our generic visitor approach is possible thanks to \K's meta-representation
of syntax as \texttt{KLabel}s and applications of them to \texttt{KList}s.

Our current visitor has an API consisting of three \texttt{KLabel}s:
\begin{itemize}
\item \texttt{\#visit}, which is expected to take two arguments, the K term
to visit and the actual visitor.
\item \texttt{\#visitor}, which is a \texttt{KItem} stating what to do during
the visit.  Currently, \texttt{\#visitor} expects four arguments:
the first two describe the action to take, and the later two describe the
condition under which to take the action.
We need two arguments for each because both the action and the condition
consist of a \texttt{KLabel} and a partial list of arguments for it.
The complete list of arguments is obtained by appending the actual node being
visited to the partial list of arguments.
\item \texttt{\#visited}, which is a wrapper for the visited K term.
\end{itemize}

One important aspect of \K visitors is that they need to allow for code
(i.e., K terms) to be executed during the visiting process.
For example, in an implementation of \texttt{quote}/\texttt{unquote} using
visitors, code which is unquoted the right number of times (as many times as
it has been quoted) has to be executed in exactly that context.
This is achieved by simply allowing the action embedded in the visitor to
do anything, including replacing the visited node with code to be executed,
in particular with itself.
In order for this to work, the temporary constructs used during the top-down
traversal saying that the term is being visited need to be made strict.
Once the argument subterms of these strict operators are visited, the larger
term is also marked visited and the process continues until the entire term
is marked as visited.
The \texttt{\#visited} label needs to yield \texttt{KResult}s in order for
this to work, although in practice probably users of the visitor will subsort
\texttt{\#visited}-wrapped terms to their definition's particular
\texttt{KResult}s.  */

module K-VISITOR
  imports K-EQUAL-HOOKS
  imports BUILTIN-HOOKS

  syntax KItem  ::= #label(KLabel)       // Should be eventually builtin
  syntax KLabel ::= "#klist"             // Should be predefined, with many others

//@ This is the API of the generic visitor:
  syntax KLabel ::= "#visit"
  syntax KLabel ::= "#visitor"
  syntax KLabel ::= "#visited"

/*@ \texttt{\#visitor} takes an action and a predicate, and \texttt{\#visit}
applies the action on each visited \texttt{KItem} that satisfies the predicate.
The action and the predicate can be regarded as curried functions, taking the
\texttt{KItem} being visited as final argument:  */

  rule #visit(L:KLabel(Kl:KList),,
              #visitor(#label(A:KLabel),,#klist(Kla:KList),,
                       #label(P:KLabel),,#klist(Klp:KList)))
    => #if P(Klp,,L(Kl)) ==K true
       #then A(Kla,,L(Kl))
       #else #visiting.kapp(#label(L),,#visit(#klist(Kl),,
                            #visitor(#label(A),,#klist(Kla),,#label(P),,#klist(Klp))))
       #fi
    when #label(L) =/=K #label(#klist)  [structural]
  rule #visit(K:KItem ~> Kr,,Vz:KItem) => #visiting.kseq(#visit(K,,Vz),,#visit(Kr,,Vz))
    when Kr =/=K .K  [structural]
  rule #visit(#klist(.KList),,Vz:KItem) => #visited(.KList)  [structural]
  rule #visit(#klist(K:K,,Kl:KList),,Vz:KItem)
    => #visiting.klist(#visit(K,,Vz),,#visit(#klist(Kl),,Vz))  [structural]

  rule isKResult(#visited(_:KList)) => true

/*@ The rules above make the visitor apply top-down.
The next rules propagate the visited status bottom-up.
For example, \texttt{\#visiting.kapp} takes a \texttt{KLabel}
represented as a \texttt{KItem} and a visited \texttt{KList}, and
yields the visited \texttt{KItem} obtained by applying the
\texttt{KLabel} to the \texttt{KList}.  */

  syntax KLabel ::= "#visiting.kapp"     // [strict(2)]
  syntax KLabel ::= "#visiting.kseq"     // [strict]
  syntax KLabel ::= "#visiting.klist"    // [strict]

// Due to bugs, the strictness attributes above don't work, so we need the following
  context #visiting.kapp(_:KItem,,HOLE)  // the first argument should be a KToken
  context #visiting.klist(_,,HOLE)
  context #visiting.klist(HOLE,,_)
  context #visiting.kseq(_,,HOLE)
  context #visiting.kseq(HOLE,,_)

  rule #visiting.kapp(#label(L),,#visited(Kl:KList)) => #visited(L(Kl))
     [structural]
  rule #visiting.klist(#visited(Kl:KList),,#visited(Kl':KList)) => #visited(Kl,,Kl')
     [structural]
  rule #visiting.kseq(#visited(K1:K),,#visited(K2:K)) => #visited(K1 ~> K2)
     [structural]
endmodule
