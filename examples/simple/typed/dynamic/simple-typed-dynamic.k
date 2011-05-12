
in simple-typed-dynamic-syntax
in ../simple-typed-programs
in simple-typed-dynamic-semantics

-----------------------------------------
--- Main module, including everything ---
-----------------------------------------

kmod SIMPLE-TYPED-DYNAMIC is including SIMPLE-TYPED-DYNAMIC-SEMANTICS + SIMPLE-TYPED-PROGRAMS 
  syntax Bag ::= run ( KLabel )
  macro run(PgmName:KLabel) =
          <T_>
             <k> PgmName(.List{K}) </k>
             <in> List(7,,23,,654,,656,,54,,456,,436345647643567,,354654364356,,4357643576) </in>
          <_/T>
endkm
