in skool-untyped-syntax
in skool-untyped-semantics
in skool-untyped-programs



----------------------------
--- SKOOL-UNTYPED module ---
----------------------------

kmod SKOOL-UNTYPED is including SKOOL-UNTYPED-SEMANTICS + SKOOL-UNTYPED-PROGRAMS 
--- make sure the name of the final module is the capitalized version of the file name


  syntax Bag ::= run ( KLabel )

--- After loading simple-untyped-compiled into maude, type "rew run .".
---<SKOOL modified>
---  macro run(K:KLabel)
---        =
---        <T_> 
---           <k> K(.List{K}) </k>
---           <class> object </class>
---           <in>
---              List(7,,23,,654,,656,,54,,456,,436345647643567,,
---                   354654364356,,4357643576)
---           </in>
---        <_/T> 

  macro run(P:KLabel)
        =
        <T_> 
           <k> kpgm(P(.List{K})) </k>
           <in> 
              List(7,,23,,654,,656,,54,,456,,436345647643567,,
                   354654364356,,4357643576)
           </in>
           <class> object </class>
           <pgm>
               <classes>
                       <className> object </className>
                       <fields> .K </fields>
               </classes>
           </pgm>
        <_/T> 
---</SKOOL modified>
endkm



