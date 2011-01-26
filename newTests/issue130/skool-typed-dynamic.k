in ../../k-prelude
in skool-typed-dynamic-syntax
in skool-typed-dynamic-semantics

----------------------------
--- SKOOL-UNTYPED module ---
----------------------------

kmod SKOOL-TYPED-DYNAMIC is
  including SKOOL-TYPED-DYNAMIC-SEMANTICS

  syntax Bag ::= run ( KLabel )

  macro run(P:KLabel)
        =
        <T_> 
           <k> P(.List{K}) </k>
           <in> 
              List(7,,23,,654,,656,,54,,456,,436345647643567,,
                   354654364356,,4357643576)
           </in>
        <_/T> 
endkm



