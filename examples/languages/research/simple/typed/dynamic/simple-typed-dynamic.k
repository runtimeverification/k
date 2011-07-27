
in simple-typed-dynamic-syntax
in ../simple-typed-programs
in simple-typed-dynamic-semantics

-----------------------------------------
--- Main module, including everything ---
-----------------------------------------

kmod SIMPLE-TYPED-DYNAMIC is including SIMPLE-TYPED-DYNAMIC-SEMANTICS + SIMPLE-TYPED-PROGRAMS 
//@ \section{Putting Them All Together}
  syntax Bag ::= run ( KLabel ) | run ( KLabel , List )
  macro run(PgmName:KLabel) =
          <T>...
             <k> PgmName(.List{K}) ~> execute </k>
          ...</T>
  macro run(PgmName,Input) =
          <T>...
             <k> PgmName(.List{K}) ~> execute </k>
             <in> Input:List </in>
          ...</T>
endkm

