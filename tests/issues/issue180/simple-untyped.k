
in simple-untyped-syntax
in simple-untyped-programs
in simple-untyped-semantics

-----------------------------------------
--- Main module, including everything ---
-----------------------------------------


module SIMPLE-UNTYPED imports SIMPLE-UNTYPED-SEMANTICS + SIMPLE-UNTYPED-PROGRAMS 
  syntax Bag ::= run ( KLabel )
  macro run(PgmName:KLabel) =
          <T_>
             <k> PgmName(.List{K}) ~> execute </k>
          <_/T>
end module
