in ../../../k-prelude
in simple-untyped-syntax
in simple-untyped-programs
in simple-untyped-semantics

-----------------------------------------
--- Main module, including everything ---
-----------------------------------------

kmod SIMPLE-UNTYPED is including SIMPLE-UNTYPED-SEMANTICS + SIMPLE-UNTYPED-PROGRAMS 
  syntax Bag ::= run ( KLabel )
  macro run(PgmName:KLabel) =
          <T_>
             <k> PgmName(.List{K}) ~> execute </k>
             <in> List(7,,23,,654,,656,,54,,456,,436345647643567,,354654364356,,4357643576) </in>
          <_/T>
endkm
