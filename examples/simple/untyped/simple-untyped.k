in ../../../k-prelude
in simple-untyped-syntax
in simple-untyped-programs
in simple-untyped-semantics

-----------------------------------------
--- Main module, including everything ---
-----------------------------------------

kmod SIMPLE-UNTYPED is
  including SIMPLE-UNTYPED-SEMANTICS + SIMPLE-UNTYPED-PROGRAMS

/*@ This module puts everything together, namely syntax, semantics and
programs (note that it includes the SIMPLE semantics, which includes
the syntax, and the SIMPLE programs).  In the current implementation
of the \K framework, the programs in the module SIMPLE-UNTYPED-PROGRAMS
are given through macros of the form ``\texttt{macro pgm = ...}'',
where \texttt{pgm} is a syntactic constant of sort \textit{Stmts} and
where the dots stand for the actual program.  For example,*/

/*@\begin{Verbatim}{frame=single}
  macro pFactorial =
       var x;

       function f(y) {
         var t=1;
         for i = 1 to y do
	   t = t*i;
	 return t;
       }

       function main() {
         x = 5;
	 write(f(f(x)));
       }
\end{Verbatim}*/

/*@As explained in the overview paper mentioned in the preamble of this
language definition, the syntax plays no special role in \K; that is,
the application of rules takes into account only the structure of the
configuration, and not how the particular current program or fragment
of program is parsed.  That means, in particular, that the distinction
between concrete/abstract syntax and its representation as computational
structure terms of sort $K$ is irrelevant in the theory of \K.  However, it
becomes quite relevant in implementations of \K tools, because one would
like to use the defined language syntax as much as possible in the semantics,
as we did in all the \K rules above, which means that one needs to combine a
parser for the defined language with a parser for \K in order to parse the
semantic rules, which is a highly non-trivial engineering endeavour.
In our current implementation of \K, the internal representation of the
terms over the user-defined syntax

syntactic 

sort language syntax terms is 



The two configuration generator operations below are meant to help
users initialize the configuration when executing programs, and not to
be regarded as part of the SIMPLE semantics.


 */

  syntax Bag ::= run ( KLabel ) | run ( KLabel , List )
  macro run(PgmName:KLabel) =
          <T_>
             <k> PgmName(.List{K}) ~> execute </k>
          <_/T>
  macro run(PgmName,Input) =
          <T_>
             <k> PgmName(.List{K}) ~> execute </k>
             <in> Input:List </in>
          <_/T>
endkm
