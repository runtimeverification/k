require "../basic/cink-basic-syntax.k"
require "../basic/cink-basic-semantics.k"
require "../l-r-values/cink-l-r-values.k"

module CINK-POINTERS-SYNTAX

  imports CINK-BASIC-SYNTAX

  syntax Exp ::= "*" Exp [indirect]
               | "&" Exp [ampersand]

  syntax priorities  indirect  > assign read write greatthan lessequal
  syntax priorities  ampersand > assign read write greatthan lessequal

endmodule

module CINK-POINTERS-SEMANTICS

  imports CINK-POINTERS-SYNTAX
  imports CINK-BASIC-SEMANTICS
  imports CINK-L-R-VALUES-SEMANTICS

  syntax PtrType ::= "pointer" "to" Type 

  syntax Type ::= PtrType

  syntax Stmt ::= Exp "of" PtrType ";"

  rule T:Type * X:Exp; => X of pointer to T;

  rule *X:Exp of PT:PtrType; => X of pointer to PT;

  rule <k> X:Id of T:PtrType; => .  ...</k>      
       <env> Env:Map => Env[L/X] </env>
       <store>... . => (L |-> undefined) ...</store>
  when fresh(L:Loc)
       [ptr-decl, structural]

  /*@
  Declaration of an alias:
  */

  context _:PrimType & _:Id = (HOLE => lvalue(HOLE));

  rule <k> T:PrimType & X:Id = L:Loc; => . ...</k>
       <env> Env:Map => Env[L/X] </env>

  context *(HOLE => lvalue(HOLE))
  context lvalue(*(HOLE => lvalue(HOLE)))

  rule <k> lvalue((* L:Loc) => L' ) ...</k>
       <store>... L |-> L':Loc ...</store> 

  rule <k> * L:Loc => V ...</k>
       <store>... L |-> L':Loc  L' |-> V:Val ...</store>

  rule isAliasExp(& E:Exp) => true

  context lvalue(&(HOLE => lvalue(HOLE)))

  rule lvalue((& L:Loc) => L ) 

  rule <k> & X:Id => L ...</k>
       <env>... X |-> L:Loc ...</env>
  
endmodule
