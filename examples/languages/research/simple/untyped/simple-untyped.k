in simple-untyped-syntax
in simple-untyped-semantics

-----------------------------------------
--- Main module, including everything ---
-----------------------------------------

module SIMPLE-UNTYPED
  imports SIMPLE-UNTYPED-SEMANTICS 

/*@ \section{Putting Them All Together} This module puts everything together,
namely syntax, semantics and programs (note that it includes the SIMPLE
semantics, which includes the syntax, and the SIMPLE programs).  It also
defines two configuration initializers, one taking only a program and one
taking a program and an input.  See the README file under k-framework for
more information on configuration initializers.  */

  syntax Bag ::= run ( KLabel ) | run ( KLabel , List )
  macro run(PgmName:KLabel) =  run(PgmName, .List)
  macro run(PgmName,Input) =
          <T>...
             <k> PgmName(.List{K}) ~> execute </k>
             <in> Input:List </in>
          ...</T>
end module
