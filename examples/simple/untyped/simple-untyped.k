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
the syntax, and the SIMPLE programs). */

/*@ \paragraph{Implementation-specific note:}
To use the semantics, for example to execute the programs defined in the
\texttt{SIMPLE-UNTYPED-PROGRAMS}, one needs to create initial configurations
holding the programs one wants to execute and possibly other data, such as,
for example, the program input.  This can be quite tedious.
%
The two configuration generator operations below are meant to help
users initialize the configuration when executing programs, and not to
be regarded as part of the SIMPLE semantics: */

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

/*@ Note that the configurations above use ruptured cells, so they take advantage of
\K's configuration abstraction mechanism.  They will be automatically completed and
initialized to match the declared configuration of SIMPLE.  To run our sample program
\texttt{pFactorial}, all we need to do (after compilation and loading the generated
Maude file) is to type in the command ``\texttt{rewrite 'pFactorial}''. */
endkm
