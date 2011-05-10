require cink-syntax
kmod CINK-SEMANTICS is including CINK-DESUGARED-SYNTAX + PL-CONVERSION 

  /*@ \subsubsection*{ASTs which are results.} */
  syntax Val ::= Int | void 
  syntax Exp ::= Val 
  syntax List{Val} ::= Val | List{Val} , List{Val} [ditto] 
  syntax List{Exp} ::= List{Val} 
  syntax KResult ::= List{Val} 

  /*@
      Any syntactic constructs which follows to be evaluated/executed,
      is declared to as being a subsort of K.
  */

  syntax K ::= List{Exp}
             | List{Id}
             | List{DeclId}
             | StmtList
             | Pgm
             | String

  /*@ \subsubsection*{Auxiliary constructs.} */
             
  syntax K ::= initial
             | restore ( Map , Map )
             | restore ( Map )
             | clearAutoStorage
             | endOfFunction
  syntax Nat ::= initialLoc

  rule initialLoc => 1 [structural]
  rule initial => 0 [structural]



  configuration <T color="red">
                  <k color="green"> .K </k>
                  <env color="pink"> .Map </env>
                  <funs color="orange"> .Map </funs> @latex("\\kBR")
                  <in color="magenta"> .List </in>
                  <out color="brown"> "" </out>
                  <mem color="yellow"> .Map </mem>
                  <ptr color="cyan"> .Map </ptr>
                  <next color="gray"> initialLoc </next>  
                  <struct color="orange"> .Map </struct>
                </T>

  /*@ \subsubsection*{Expressions Evaluation.} */ 
  rule I1:Int == I2:Int => Bool2Int(I1 ==Int I2) [structural] 
  rule I1 != I2 =>  Bool2Int((I1 !=Int I2)) [structural]
  rule I1 + I2 => I1 +Int I2 [structural]
  rule I1 - I2 => _-Int_(I1,I2) [structural]
  rule I1 <= I2 => Bool2Int(I1 <=Int I2) [structural]
  rule I1 < I2 => Bool2Int(I1 <Int I2) [structural]
  rule '_?_:_ => 'if`(_`)_else_  [structural]

  syntax Nat ::= offset ( StmtList , Id )
  rule offset(__(_;(int_(F)), Fl), F) => 0 [structural]
  rule offset(_;(int_(F)), F) => 0 [structural]
  rule offset(__(_;(int_(F':Id)), Fl), F) => 1 +Nat offset(Fl, F) if F =/=Bool F' [structural]
  rule offset(__(_;(int_(*_(F))), Fl), F) => 0 [structural]
  rule offset(_;(int_(*_(F))), F) => 0 [structural]
  rule offset(__(_;(int_(*_(F'))), Fl), F) => 1 +Nat offset(Fl, F) if F =/=Bool F' [structural]
  rule offset(__(_;(struct__(Struct, *_(F))), Fl), F) => 0 [structural]
  rule offset(__(_;(struct__(Struct, *_(F'))), Fl), F) => 1 +Nat offset(Fl, F) if F =/=Bool F' [structural]

  rule <k> _._(X, F:Id) => *(L +Nat offset(Fl, F)) <_/k>
       <env_> X |-> tl(L, struct Struct) <_/env>
       <struct_> Struct |-> {Fl} <_/struct>


  rule <k> &_(_._(X, F:Id)) => L +Nat offset(Fl, F) <_/k>
       <env_> X |-> tl(L, struct Struct) <_/env>
       <struct_> Struct |-> {Fl} <_/struct>

/*@ \subsubsection*{Declarations.} */
  rule [var-decl] :
       <k> int X => void <_/k>
       <env_> . => (X |-> L) <_/env>
       <mem_> . => (L |-> initial) <_/mem>
       <next> L => L +Nat 1 </next>
       [structural large]

  rule [array-decl] :
       <k> int *(X + N) => void <_/k>
       <env_> . => (X |-> L) <_/env> @latex("\\kBR")
       <mem_> . => (L |-> L +Nat 1 L +Nat 1..L +Nat N +Nat 1 |-> initial) <_/mem>
       <next> L => L +Nat N +Nat 1 </next>
       [structural large]

  rule [fun-decl] :
       <k> _`(_`)`{_`}(int X, Xl:List{DeclId}, Sts) => . <_/k> 
       <funs_> . => X |-> int X(Xl:List{DeclId}) { Sts } <_/funs> 
       [structural]

  rule [include] :
       <k> #include <stdio.h> => . <_/k>

  rule [struct-decl] :
       <k> struct_`{_`};(X, Fl:StmtList) => . <_/k>
       <struct_> . => (X |-> {Fl}) <_/struct> 

  rule [var-decl] :
       <k> struct Struct *X => void <_/k>
       <env_> . => (X |-> L) <_/env>
       <mem_> . => (L |-> initial) <_/mem>
       <next> L => L +Nat 1 </next>
       [structural]
/*
  rule [var-decl] :
       <k> struct Struct:Id X => mergeNames(X, Fl)~>void <_/k>
       <env_> . => (X |-> L) <_/env>
       <struct_> Struct |-> {Fl} <_/struct>
       <next> L </next>
       [structural]

  rule [var-decl] :
       <k> int_(_._(X, E)) => void <_/k>
       <env_> (X |-> L':Nat) (. => (L'.E |-> L)) <_/env>
       <mem_> . => (L |-> initial) <_/mem>
       <next> L => L +Nat 1 </next>
       [structural]

  syntax K ::= mergeNames ( Id , StmtList )
  rule mergeNames(X, (Stmt Stmts) ) => mergeNames(X, Stmt)~>mergeNames(X, Stmts) [structural] 
  rule mergeNames(X, (int E:Exp;) ) => _;(int_(X.E)) [structural] 
  rule mergeNames(X, (struct Struct E:Exp;) ) => _;(struct__(Struct, X.E)) [structural]
*/

//  syntax Type ::= int | int * | struct Id | struct Id * 
  syntax K ::= tl ( Nat , struct Id )
  syntax Nat ::= noFields ( StmtList )
  rule noFields(Stmt:Stmt Stmts:StmtList) => 1 +Nat noFields(Stmts) [structural] 
  rule noFields(int E;) => 1 [structural]
  rule noFields(struct Struct *F;) => 1 [structural]

  rule [var-decl] :
       <k> struct Struct:Id X => void <_/k>
       <env_> . => (X |-> tl(L, struct Struct)) <_/env>
       <struct_> Struct |-> {Fl} <_/struct>
       <mem_> . => (L..L +Nat noFields(Fl) |-> initial) <_/mem>
       <next> L => L +Nat noFields(Fl) </next>
       [structural]


  /*@ \subsubsection*{Memmory operations.} */
  rule [mem-lookup] :
       <k> X:Id => V <_/k>
       <env_> X |-> L <_/env>
       <mem_> L |-> V <_/mem>
       [structural]

  rule [mem-lookup] :
       <k> *L:Nat => V <_/k>
       <mem_> L |-> V <_/mem>
       [structural]

  rule [reference] :
       <k> & X => L <_/k>
       <env_> X |-> L <_/env>
       [structural]

  rule [dereference] :
       <k>  & * E => E <_/k>
       [structural]

  context [HOLE] = _
  rule [mem-update] :
       <k> L = V => V <_/k>
       <mem_> L |-> (_ => V) <_/mem>
       [structural]

  /*@ \subsubsection*{Control Statements.} */
  rule [while] :
       <k>
           while(E:Exp) St => if (E) {St while(E) St} else {}
       <_/k>
       [structural]
  rule [if-false] : if(I)_ else St:Stmt => St if I ==Int 0 [structural]
  rule [if-true] : if(I:Int) St else _ => St if notBool(I ==Int 0) [structural]
  rule [instr-expr] : V:Val ; => . [structural]

  rule [block] : <k> {Sts:StmtList} => Sts <_/k>  [structural]
  rule [block-empty] : {} => .  [structural]
  rule [seq-comp] : <k> St Sts => St ~> Sts <_/k> [structural] 

  /*@ \subsubsection*{Input/Output Statements.} */
  rule [print]:
       <k> printf("%d;",I) => void <_/k>
       <out> S:String => S +String Int2String(I) +String ";" </out>

  rule [read-local]:
       <k> scanf("%d",L) => void <_/k>
       <mem_> L |-> (_ => I) <_/mem>
       <in> (ListItem(I) => .) <_/in>

 /*@ \subsubsection*{Function Call.} */
  rule [fun-call] : 
      <k> '_`(_`)(X,,Vl:List{Val})
           =>
           Sts ~> endOfFunction ~> restore(Env:Map)
       <_/k>  
       <env> Env        
             =>
             (eraseKLabel('*_, eraseKLabel('int_, getList{K}(Xl))) |->
              L..L +Nat lengthList{K}(getList{K}(Vl))
             )
       </env> @latex("\\kBR")
       <mem_> .
             =>
             (L..L +Nat lengthList{K}(getList{K}(Vl)) |-> getList{K}(Vl))
       <_/mem> 
       <next> L => L +Nat lengthList{K}(getList{K}(Vl)) </next>
       <funs_> X |->  int X(Xl) { Sts } <_/funs>
       [structural large]

  /*@ \subsubsection*{Function Return.} */
  rule [return-middle] :
       <k> return E ; ~> (K:K => .) <_/k>
       if K =/=Bool endOfFunction
  rule [return-last] :
       <k> (return E ; ~> endOfFunction) => E <_/k>
  rule [no-return] :<k> endOfFunction => . <_/k>


  rule [nonvoid-fun-return] :
       <k> V ~> (restore(Env) => .) <_/k>
       <env> _ => Env </env>


  rule [void-fun-return] :
       <k> restore(Env) => void <_/k>
       <env> _ => Env </env>
       [structural]

  /*@ \subsubsection*{The Management of the Dynamic Memory.} */
  rule [malloc]: 
       <k> (int *)malloc(N:Nat*sizeof(int)) => L:Nat <_/k>
       <ptr_> . => L |-> N <_/ptr>
       <mem_> . => L..L +Nat N |-> initial <_/mem>
       <next> L => L +Nat N </next>  
   [structural]


  rule [malloc]: 
       <k> (struct Struct *)malloc(N:Nat*sizeof(struct Struct)) => L:Nat <_/k>
       <ptr_> . => L |-> N <_/ptr>
       <mem_> . => L..L +Nat (N *Nat noFields(Fl)) |-> initial <_/mem>
       <struct_> Struct |-> {Fl} <_/struct>
       <next> L => L +Nat (N *Nat noFields(Fl)) </next>  
   [structural]
 
  rule [malloc]: 
       <k> (struct Struct *)malloc(N:Nat*sizeof(struct Struct)) => L:Nat <_/k>
       <ptr_> . => L |-> N <_/ptr>
       <mem_> . => L..L +Nat (N *Nat noFields(Fl)) |-> initial <_/mem>
       <struct_> Struct |-> {Fl} <_/struct>
       <next> L => L +Nat (N *Nat noFields(Fl)) </next>  
   [structural]


  rule [free]:
       <k> free(L) => void <_/k>
       <ptr_> L |-> N => . <_/ptr>
       <mem> Mem:Map => Mem[undef/L..L+Nat N] </mem>
       [structural]

  /*@ \subsubsection*{Auxiliary Functions.} */
  syntax List{K} ::= Nat .. Nat
  rule N1:Nat..N1 => .List{K} [structural]
  rule N1..sNat(N) => N:Nat,, N1..N [structural]

endkm

