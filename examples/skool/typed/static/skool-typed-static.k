in ../../../../k-prelude
in skool-typed-static-syntax
in skool-typed-static-semantics
in ../skool-typed-programs

----------------------------
--- SKOOL-UNTYPED module ---
----------------------------

kmod SKOOL-TYPED-STATIC is
   including SKOOL-TYPED-STATIC-SEMANTICS + SKOOL-TYPED-PROGRAMS 
--- make sure the name of the final module is the capitalized version of the file name


  syntax Bag ::= run ( KLabel )

  macro run(P:KLabel)
        =
        <T_> 
           <pgm> P(.List{K}) </pgm>
        <_/T> 
---</SKOOL modified>
endkm




