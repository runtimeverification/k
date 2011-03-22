in ../../../k-prelude
in simple-untyped-syntax
in simple-untyped-programs
in simple-untyped-semantics

-----------------------------------------
--- Main module, including everything ---
-----------------------------------------


kmod SIMPLE-UNTYPED-INPUT-TEST is including SIMPLE-UNTYPED-SEMANTICS

  syntax List ::= input 

  macro input = 
List(7,,3,,
654,,656,,54,,456,,436345647643567,,354654364356,,4357643576,,
654,,656,,54,,456,,436345647643567,,354654364356,,4357643576,,
654,,656,,54,,456,,436345647643567,,354654364356,,4357643576
)

endkm

kmod SIMPLE-UNTYPED is including SIMPLE-UNTYPED-SEMANTICS + SIMPLE-UNTYPED-PROGRAMS + SIMPLE-UNTYPED-INPUT-TEST 
  syntax Bag ::= run ( KLabel )
  macro run(PgmName:KLabel) =
          <T_>
             <k> PgmName(.List{K}) ~> execute </k>
             <in> input </in>
          <_/T>
endkm
