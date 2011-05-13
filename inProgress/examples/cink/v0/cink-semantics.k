require cink-syntax

kmod CINK-SEMANTICS is including CINK-DESUGARED-SYNTAX + PL-CONVERSION 

  /*@\subsubsection*{ASTs which are results.} */
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
             | restore ( Map )
             | endOfFunction
  rule initial => 0 [structural]

  configuration <T>
                  <k> .K </k>
                  <env> .Map </env>
                  <funs> .Map </funs> @latex("\\kBR")
                  <in> .List </in>
                  <out> "" </out> 
                </T>
  
  /*@\subsubsection*{Expressions Evaluation.} */
  rule I1 + I2 => _+Int_(I1,I2) [structural]
  rule I1 - I2 => _-Int_(I1,I2) [structural]
  rule I1:Int * I2:Int => I1 *Int I2 [structural]
  rule I1 > I2 => Bool2Int(I1 >Int I2) [structural]

  /*@ \subsubsection*{Declarations.} */
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

  /*@ \subsubsection*{Memmory operations.} */
  rule [mem-lookup] :
       <k> X:Id => V <_/k>
       <env_> X |-> V <_/env>
       [structural]

  rule [mem-update] :
       <k> X = V => V <_/k>
       <env_> X |-> (_ => V) <_/env>
       [structural]

  /*@ \subsubsection*{Control Statements.} */
  rule [while]:
       <k> while(E:Exp) St => if (E) {St while(E) St} else {} <_/k>
       [structural]

  rule [if-false] : if(I:Int)_ else St:Stmt => St if I ==Int 0 [structural]
  rule [if-true] : if(I) St else _ => St if notBool(I ==Int 0) [structural]
  rule [instr-expr] : V:Val ; => . [structural]

  rule [block] : {Sts:StmtList} => Sts  [structural]
  rule [block-empty] : {} => .  [structural]
  rule [seq-comp] : St Sts => St ~> Sts [structural] 

  /*@ \subsubsection*{Input/Output Statements.} */
  rule [read-local]:
       <k> scanf("%d",& X) => void <_/k>
       <env_> X |-> (_ => I) <_/env>
       <in> (ListItem(I) => .) <_/in>

  rule [print]:
       <k> printf("%d;",I) => void <_/k>
       <out> S:String => S +String Int2String(I) +String ";" </out>


 /*@ \subsubsection*{Function Call.} */
 rule [fun-call] : 
       <k> '_`(_`)(X,,Vl:List{Val})
           =>
           Sts ~> endOfFunction ~> restore(Env:Map)
       <_/k> 
       <env> Env
             =>
             (varNameList(getList{K}(Xl)) |-> getList{K}(Vl))
       </env>
       @latex("\\kBR")
       <funs_> X |->  int X(Xl) { Sts } <_/funs>
       [structural large]

  /*@ \subsubsection*{Function Return.} */
  rule [return-middle] :
       <k> return E ; ~> (K:K => .) <_/k>
       if K =/=Bool endOfFunction
  rule [return-last] :
       <k> (return E ; ~> endOfFunction) => E <_/k>

  rule [no-return] : <k> endOfFunction => . <_/k>

  rule [nonvoid-fun-return] :
       <k> V ~> (restore(Env) => .) <_/k>
       <env> _ => Env </env>
       [structural]

  rule [void-fun-return] :
       <k> restore(Env) => . <_/k>
       <env> _ => Env </env>
       [structural]


  /*@ \subsubsection*{Auxiliary Functions.} */
  syntax List{K} ::= Nat .. Nat
  rule N1:Nat..N1 => .List{K} [structural]
  rule N1..sNat(N) => N:Nat,,N1..N [structural]

  syntax List{K} ::= varNameList ( List{K} )
  rule varNameList(Kl:List{K}) => eraseKLabel('int_, Kl) [structural]

endkm

