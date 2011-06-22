
in simple-untyped-syntax
in simple-untyped-programs
in simple-untyped-semantics

-----------------------------------------
--- Main module, including everything ---
-----------------------------------------

kmod SIMPLE-UNTYPED is
  including SIMPLE-UNTYPED-SEMANTICS + SIMPLE-UNTYPED-PROGRAMS

/*@ \section{Putting Them All Together} This module puts everything together,
namely syntax, semantics and programs (note that it includes the SIMPLE
semantics, which includes the syntax, and the SIMPLE programs).  It also
defines two configuration initializers, one taking only a program and one
taking a program and an input.  See the README file under k-framework for
more information on configuration initializers.  */

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
