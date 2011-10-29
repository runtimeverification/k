module EASY-SYNTAX
//0.1
//@2.1  syntax Stmt ::= "write" ( #String ) 
//1.1
  syntax Stmt ::= Stmt ";" Stmt   // statement sequencing
//2.1 
//@3.4  syntax Stmt ::= "write" ( Exp ) 
  syntax Exp ::= #String 
//@3.5               | Exp + Exp
//3.1
  syntax Exp ::= #Id
  syntax Stmt ::= var #Id 
                | #Id := Exp
//3.4
  syntax Stmt ::= "write" ( Exp ) [strict]
//3.5
  syntax Exp ::= Exp + Exp [strict]
//4.1
  syntax Ids ::= List{#Id,","}
  syntax Exps ::= List{Exp,","}
  syntax Stmt ::= procedure #Id Ids ; begin Stmt end
                | call #Id Exps
//5.1
                | spawn #Id Exps
end module

//0.2

module EASY imports EASY-SYNTAX
/*@1
  configuration 
    <k> $PGM:K </k>
*/

//1
/*@3.2
  configuration 
    <k> $PGM:K </k> 
    <out> .List </out>
*/

  rule 
    <k> write(S:#String) => . ...</k> 
    <out>... . => ListItem(S) </out>

//2
  rule 
    St1:Stmt ;  St2:Stmt => St1 ~> St2

//3
  rule
    S1:#String + S2:#String => S1 +String S2

//3.2
/*@4.2
  configuration 
    <k> $PGM:K </k> 
    <env> .Map </env> 
    <out> .List </out>
*/

  rule 
    <k> var X:#Id => . ...</k> 
    <env>... .Map => X |-> "" ...</env>

//3.3
  rule 
    <k> X:#Id := S:#String => . ...</k>
    <env>... X |-> (_ => S) ...</env>   

//3.6
  syntax KResult ::= #String

//4
  rule
    <k> X:#Id => K:K ...</k>
    <env>... X |-> K ...</env>

//4.2
/*@5.1
  configuration
    <k> $PGM:K </k> 
    <env> .Map </env> 
    <out> .List </out>
    <procs> .Map </procs>
*/

  rule 
    <k> procedure X:#Id Xs:Ids ; begin St:Stmt end => . ...</k>
    <procs>... . => X |-> (bindTo(Xs) ~> St) ...</procs>

  syntax K ::= bindTo Ids

//4.3
  rule 
    <k> call X:#Id Vs:Vals => Vs ~> K ~> env(Env) ...</k>
    <env> Env:Map => . </env>
    <procs>... X |-> K:K ...</procs>

  syntax K ::= env ( Map )
  syntax Val ::= #String
  syntax Exp ::= Val
  syntax KResult ::= Val
  syntax Vals ::= List{Val,","}

//4.4
  rule 
    <k> (V:Val,Vs:Vals => Vs) ~> bindTo(X:#Id,Xs:Ids => Xs) ...</k>
    <env>... . => X |-> V ...</env>

//4.5
  rule .Vals ~> bindTo(.Ids) => .

//5
  rule 
    <k> env(Env:Map) => . ...</k>
    <env> _ => Env </env>

//5.1
  configuration
    <thread multiplicity="*">
      <k> $PGM:K </k> 
      <env> .Map </env> 
    </thread>
    <out> .List </out>
    <procs> .Map </procs>
 
  rule 
    <k> spawn X:#Id Vs:Vals => . ...</k>
    <procs>... X |-> K:K ...</procs>
    (. => <thread>... <k> Vs ~> K </k> ...</thread>)

//5.2
  rule
    <thread>... <k> .K </k> ...</thread> => .
end module

