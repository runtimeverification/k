require cink-syntax
require solver

kmod CINK-SEMANTICS is including CINK-DESUGARED-SYNTAX + PL-CONVERSION + K-WRAPPERS + SOLVER

  //@ \subsubsection{ASTs which are results.}
  syntax Val ::= ExpInt | void 
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
             | ExpBool
             | lockVar

  //@ \subsubsection{Auxiliary constructs.}
  syntax Nat ::= initialLoc
  syntax K ::= initial
             | restore ( Map )
             | increment ( Nat , Nat )
             | endOfFunction
             | error

  kvar Path : List
  kvar EB EB' : ExpBool
  kvar I : ExpInt
  kvar Mem : Map

  configuration <T>
                  <config multiplicity="*">
                    <k> .K </k>
                    <env> .Map </env>
                    <in> .List </in>
                    <out> "" </out>
                    <path> .List </path> 
                    <constr> true </constr> 
                    <lock> 0 </lock>
                  </config>@latex("\\kBR")
                  <funs> .Map </funs> 
                  <infeasible> 0 </infeasible> 
                  <infPaths> .Map </infPaths>
                  <nextSymVar> 0 </nextSymVar>
                </T>
  
  
 
  //@ Path labels
  syntax ListItem ::= ifThen | ifElse | whileTrue | whileFalse | endFun


  //@ \subsubsection{Expressions Evaluation.}
  rule I1:ExpInt + I2:ExpInt => I1 +Int I2 [structural]
  rule I1 - I2 => _-Int_(I1,I2) [structural]
  rule I1 * I2 => I1 *Int I2 [structural]
  rule I1 > I2 => ExpBool2Int(I1 >Int I2) [structural]


  //@ \subsubsection{Declarations.}
  rule [fun-decl] :
       <k> _`(_`)`{_`}(int X, Xl:List{DeclId}, Sts) => . <_/k> 
       <funs_> . => X |-> int X(Xl:List{DeclId}) { Sts } <_/funs> 
       [structural]

   rule [var-decl] :
       <k> int X => void <_/k>
       <env_> . => (X |-> initial) <_/env>
      [structural]

  rule [include] :
       <k> #include <stdio.h> => . <_/k>

  //@ \subsubsection{Memmory operations.}
  rule [mem-lookup] :
       <k> X:Id => V <_/k>
       <env_> X |-> V <_/env>
       [structural]

  rule [mem-lookup] :
       <k> (X:Id ~> K:K) => . </k>
       <env_> X |-> initial <_/env>
       <path> Path </path>
       <out> Out => Out +String "Uninitialized variable: " +String Id2String(X) +String ". The path is: " +String String(Path) +String "."</out>
       [structural large]

  rule [mem-update] :
       <config_>
         <k> X = V => V <_/k>
         <env_> X |-> (_ => V) <_/env>
       <_/config>
       [structural]

  //@ \subsubsection{Control Statements}


  syntax K ::= assume ( ExpBool )

/*
  rule [while]:
       <k> while(E:Exp) St => if (E) {St while(E) St} else {} <_/k>
       [structural]
*/

  syntax Stmt ::= strictWhile ( Exp ) Stmt [strict(1)] 
                | endWhile ( Map ) 
                | endWhile ( Exp , Map )

  rule [while]:
       <k> while(E:Exp) St => strictWhile (E) { St endWhile(E,Mem) } <_/k>
       <env> Mem </env>
       [structural]

  rule [sWhile] :
       <config>
         <k> strictWhile(I) St ~> K:K </k>
         <path> Path </path> 
         CFG:Bag
       </config>
       =>
       (
        <config>
         <k> assume(I !=Int 0) ~> St ~> K </k>
          <path> Path whileTrue </path> 
          CFG:Bag
        </config>
        <config>
          <k> assume(I ==Int 0) ~> K </k>
          <path> Path whileFalse </path> 
          CFG:Bag
        </config>
       )

 
  rule [feasible] :
       <k> assume(EB) => . <_/k>
       <constr> EB' => (EB andBool EB') </constr>
       if search(s@lve(EB andBool EB') => s@t)

  rule [infeasible] :
       (
        <config>
          <k> assume(EB) <_/k>
          <constr> EB' </constr>
          <path> Path </path> 
          CFG
        </config> => .
       )
       <infeasible> N => N +Nat 1 </infeasible> 
       <infPaths_> . => (N |-> wlist(Path)) <_/infPaths>
       if search(s@lve(EB andBool EB') => uns@t)

  rule [infinite-cycle] :
       <k> endWhile(E,Mem':Map) => error <_/k>
       <env> Mem </env>
       <path> Path </path> 
       <out> Out:String => Out +String "Infinite cycle. The path is: " +String String(Path) +String "." </out>
       if getReduct(Mem, getVar(E)) ==Bool getReduct(Mem', getVar(E))

  rule [endwhile] :
       <k> endWhile(E,Mem') => . <_/k>
       <env> Mem </env>
       if getReduct(Mem, getVar(E)) =/=Bool getReduct(Mem', getVar(E))

/*
  rule [if-false] : if(I:ExpInt)_ else St:Stmt => St if I ==Int 0 [structural]
  rule [if-true] : if(I) St else _ => St if I !=Int 0 [structural]
*/

  rule [if]:
       <config>
         <k> if(I) St else St':Stmt ~> K:K </k>
         <path> Path </path>
         CFG:Bag
       </config>
       => 
       (
        <config>
          <k> assume(I ==Int 0) ~> St' ~> K </k>
          <path> Path ifElse </path> 
          CFG:Bag
        </config>
        <config>
          <k> assume(I !=Int 0) ~> St ~> K </k>
          <path> Path ifThen </path> 
          CFG:Bag
        </config>
       )
       [large]

  rule [instr-expr] : V:Val ; => . [structural]

  rule [block] : {Sts:StmtList} => Sts  [structural]
  rule [block-empty] : {} => .  [structural]
  rule [seq-comp] : St:Stmt Sts => St ~> Sts [structural] 

  //@ \subsubsection{Input/Output Statements.}
/*
  rule [read-local]:
       <k> scanf("%d",& X) => void <_/k>
       <env_> X |-> (_ => I) <_/env>
       <in> (ListItem(I) => .) <_/in>
*/

  rule [read-local]:
       <config_>
         <k> scanf("%d",& X) => void <_/k>
         <env_> X |-> (_ => symInt(N)) <_/env>
       <_/config>
       <nextSymVar> N:Nat => N +Nat 1 </nextSymVar>
/*
  rule [print]:
       <k> printf("%d;",I) => void <_/k>
       <out> S:String => S +String Int2String(I) +String ";" </out>
*/
  rule [print]:
       <k> printf("%d;",I) => void <_/k>


 //@ \subsubsection{Function Call.}
 rule [fun-call] : 
       <k> '_`(_`)(X,,Vl:List{Val})
           =>
           Sts ~> endOfFunction ~> restore(Env:Map)
       <_/k> 
       <env> Env
             =>
             (varNameList(getList{K}(Xl)) |-> getList{K}(Vl))
       </env>
       <path> Path => (Path ListItem(X)) </path> 
       <funs_> X |->  int X(Xl) { Sts } <_/funs>
       [structural large]

  //@ \subsubsection{Function Return.}
  rule [return-middle] :
       <k> return E:Exp ; ~> (K:K => .) <_/k>
       if K =/=Bool endOfFunction
  rule [return-last] :
       <k> (return E ; ~> endOfFunction) => E <_/k>
       <path> Path => (Path endFun) </path> 

  rule [no-return] :
       <k> endOfFunction => . <_/k>
       <path> Path => (Path endFun) </path> 

  rule [nonvoid-fun-return] :
       <k> V ~> (restore(Env) => .) <_/k>
       <env> _ => Env </env>
       [structural]

  rule [void-fun-return] :
       <k> restore(Env) => . <_/k>
       <env> _ => Env </env>
       [structural]


  rule [lock] :
       <k> lock() => void<_/k>
       <lock> 0 => 1 </lock> 

  rule [lock] :
       <k> lock() => error <_/k>
       <lock> 1 </lock> 
       <path> Path </path> 
       <out> Out => Out +String "Lock mismatched. The path is: " +String String(Path) +String "." </out>

  rule [unlock] :
       <k> unlock() => void<_/k>
       <lock> 1 => 0 </lock>

  rule [unlock] :
       <k> unlock() => error <_/k>
       <lock> 0 </lock> 
       <path> Path </path> 
       <out> Out => Out +String "Unlock mismatched. The path is: " +String String(Path) +String "." </out>

  //@ \subsubsection{Auxiliary Functions.}
  syntax List{K} ::= Nat .. Nat
  rule N1:Nat..N1 => .List{K} [structural]
  rule N1..sNat(N) => N:Nat,,N1..N [structural]

  syntax List{K} ::= varNameList ( List{K} )
  rule varNameList(Kl:List{K}) => eraseKLabel('int_, Kl) [structural]

  syntax String ::= `String ( List )
  rule String(ifThen) => "ifThen; " [structural]
  rule String(ifElse) => "ifElse; " [structural]
  rule String(whileTrue) => "whileTrue; "  [structural]
  rule String(whileFalse) => "whileFalse; " [structural]
  rule String(endFun) => "endFun; " [structural]
  rule String(.List) => "" [structural] 
  rule String(LI:ListItem L:List) => String(LI) +String String(L) if L =/=Bool .List [structural]
  rule String(ListItem(Id:Id)) => Id2String(Id) +String "; " [structural]

  syntax List{K} ::= getVar ( Exp )
  rule getVar(Int:Int) => .List{K} [structural]
  rule getVar(Id) => Id [structural]
  rule getVar(E1:Exp + E2:Exp) => getVar(E1:Exp) ,, getVar(E2:Exp) [structural]
  rule getVar(E1:Exp - E2:Exp) => getVar(E1:Exp) ,, getVar(E2:Exp) [structural]
  rule getVar(E1:Exp * E2:Exp) => getVar(E1:Exp) ,, getVar(E2:Exp) [structural]
  rule getVar(E1:Exp > E2:Exp) => getVar(E1:Exp) ,, getVar(E2:Exp) [structural]
  rule getVar(E1:Exp = E2:Exp) => getVar(E1:Exp) ,, getVar(E2:Exp) [structural]

  syntax Map ::= getReduct ( Map , List{K} )
  rule getReduct(Map:Map, .List{K}) => Map [structural] 
  rule getReduct(.Map, Kl) => .Map [structural] 
  rule getReduct((Map K1:K |-> K2:K), K1,, Kl) => K1:K |-> K2:K getReduct(Map, Kl) [structural] 
  rule getReduct(Map, K1,, Kl) => getReduct(Map, Kl) if notBool $hasMapping(Map, K1) [structural] 
  
endkm

