require cink-syntax

kmod CINK-SEMANTICS is including CINK-DESUGARED-SYNTAX + K + PL-CONVERSION 

  // ASTs which are results
  syntax Val ::= Int | void 
  syntax Exp ::= Val 
  syntax List{Val} ::= Val | List{Val} , List{Val} [ditto] 
  syntax List{Exp} ::= List{Val} 
  syntax KResult ::= List{Val} 

  /*
      Any syntactic constructs which follows to be evaluated/executed,
      is declared to as being a subsort of K.
  */

  syntax K ::= List{Exp}
             | List{Id}
             | List{DeclId}
             | StmtList
             | Pgm
             | String

  // Auxiliary constructs
  syntax Nat ::= initialLoc
  syntax K ::= initial
             | restore ( Map )
             | increment ( Nat , Nat )
             | endOfFunction

  configuration <T>
                  <k> .K </k>
                  <env> .Map </env>
                  <funs> .Map </funs> @latex("\\kBR")
                  <in> .List </in>
                  <out> "" </out>
                  <mem> .Map </mem>
                  <next> initialLoc </next>
                </T>

  // Expressions Evaluation
  rule I1 + I2 => _+Int_(I1,I2) [structural]
  rule I1 - I2 => _-Int_(I1,I2) [structural]
  rule I1:Int * I2:Int => I1 *Int I2 [structural]
  rule I1 > I2 => Bool2Int(I1 >Int I2) [structural]
  rule [increment] :
       <k> ID:Id ++ => I <_/k>
       <env_> ID |-> L:Nat <_/env>
       <mem> L |-> ( I => I +Int 1 ) <_/mem>
       [structural]

  // Declarations
  rule [fun-decl] :
       <k> _`(_`)`{_`}(int X, Xl:List{DeclId}, Sts) => . <_/k> 
       <funs_> . => X |-> int X(Xl:List{DeclId}) { Sts } <_/funs> 
       [structural]

  rule initialLoc => 1 [structural]
  rule initial => 0 [structural]

  rule [var-decl] :
       <k> int X => void <_/k>
       <env_> . => (X |-> L) <_/env>
       <mem_> . => (L |-> initial) <_/mem>
       <next> L => L +Nat 1 </next>
       [structural]

  rule [include] :
       <k> #include <stdio.h> => . <_/k>

  // Memmory operations
  rule [mem-lookup] :
       <k> X:Id => V <_/k>
       <env_> X |-> L <_/env>
       <mem_> L |-> V <_/mem>
       [structural]

  rule [mem-update] :
       <k> X = V => V <_/k>
       <env_> X |-> L <_/env>
       <mem_> L |-> (_ => V) <_/mem>
       [structural]

  //Control Statements
  rule [while]:
       <k> while(E:Exp) St => if (E) {St while(E) St} else {} <_/k>
       [structural]

  rule [if-false] : if(I:Int)_ else St:Stmt => St if I ==Int 0 [structural]
  rule [if-true] : if(I) St else _ => St if notBool(I ==Int 0) [structural]
  rule [instr-expr] : V:Val ; => . [structural]

  rule [block] : {Sts:StmtList} => Sts  [structural]
  rule [block-empty] : {} => .  [structural]
  rule [seq-comp] : St Sts => St ~> Sts [structural] 

  // Input/Output Statements
  rule [read-local]:
       <k> scanf("%d",& X) => void <_/k>
       <env_> X |-> L <_/env>
       <mem_> L |-> (_ => I) <_/mem>
       <in> (ListItem(I) => .) <_/in>

  rule [print]:
       <k> printf("%d;",I) => void <_/k>
       <out> S:String => S +String Int2String(I) +String ";" </out>


 // Function Call
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

  // Function Return
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


  // Auxiliary Functions
  syntax List{K} ::= Nat .. Nat
  rule N1:Nat..N1 => .List{K} [structural]
  rule N1..sNat(N) => N:Nat,,N1..N [structural]

  syntax List{K} ::= varNameList ( List{K} )
  rule varNameList(Kl:List{K}) => eraseKLabel('int_, Kl) [structural]

endkm

