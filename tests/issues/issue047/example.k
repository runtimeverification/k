

module SKOOL-UNTYPED-SYNTAX 

  syntax Var ::= Id 

  syntax Id ::= main | object
 
  syntax Exp  ::= 
                 Var | Int | Bool

  syntax ClassDecl ::= class Id extends Id { Stmts }
--- </OO stuff addded>

  syntax Stmt ::=
                 { } 
               | { Stmts }


  syntax Stmts ::= 
                ClassDecl
             --- </OO stuff addded>
               | Stmt
               | Stmts Stmts [prec 100 gather(e E)]

end module

--------------------------------------
--- SKOOL-UNTYPED-SEMANTICS module ---
--------------------------------------


module SKOOL-UNTYPED-SEMANTICS imports SKOOL-UNTYPED-SYNTAX 


--- We have to subsort all the syntactic categories to K, and the lists of values
--- to KResult.  Recall that the second argument of a method application is a list
--- of expressions, so that becomes a result when it becomes a list of values

  configuration <T> 
                     <k> $PGM:K </k>
                     <fstack> .List </fstack>
                     <env> .Map </env>
                     <genv> .Map </genv>
                     <store> .Map </store>
                     <in> .List </in>
                     <out> .List </out>
                     <nextLoc> 0 </nextLoc>
                     <obj> .List </obj>
                     <class> main </class>
                     <pgm>
                           <classes multiplicity="*">
                                    <className> object </className>
                                    <extends> object </extends>
                                    <fields> .K </fields>
                                    <methods> .K </methods>
                           </classes>
                     </pgm>
                </T>

end module
----------------------------
--- SKOOL-UNTYPED module ---
----------------------------

module SKOOL-UNTYPED imports SKOOL-UNTYPED-SEMANTICS


--- kpgm label is used to traverse a program and to build the content of the <pgm>..</pgm> cell
  syntax KLabel ::= kpgm

--- a class traversal
  rule <k> kpgm(class C1:Id extends C2:Id { Ss:Stmts }) => kpgm(Ss) <_/k>
       <class> C:Id => C1 </class>
       <pgm_> . => <classes_>
                           <className> C1 </className>          
                           <extends> C2 </extends>
                           <fields_> .K <_/fields>
                           <methods_> .K <_/methods>
                   <_/classes>
       <_/pgm>

end module
