in ../../../../k-prelude
in skool-typed-static-syntax
in skool-typed-static-semantics
in ../skool-typed-programs

----------------------------
--- SKOOL-UNTYPED module ---
----------------------------

kmod SKOOL-TYPED-STATIC is
   including SKOOL-TYPED-STATIC-SEMANTICS + SKOOL-TYPED-PROGRAMS 

  syntax Bag ::= run ( KLabel )

  macro run(P:KLabel)
        =
        <T_> 
           <pgm> P(.List{K}) </pgm>
        <_/T> 
endkm




