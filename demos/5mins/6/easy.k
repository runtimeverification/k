module EASY-SYNTAX
//0.1
//@2.1  syntax Stmt ::= "write" ( #String ) ;
//1.1
  syntax Stmt ::= Stmt  Stmt   [prec 90] // statement sequencing
//2.1 
//@3.4  syntax Stmt ::= "write" ( Exp ) ;
  syntax Exp ::= #String 
//@3.5               | Exp + Exp
//3.1
  syntax Exp ::= #Id
  syntax Stmt ::= var #Id ;
//@4.6                | #Id := Exp ; [prec 80]
//3.4
  syntax Stmt ::= "write" ( Exp ) ; [strict]
//3.5
  syntax Exp ::= Exp + Exp [strict prec 50]
//3.6
  syntax Val ::= #String
  syntax Exp ::= Val
//4.1
  syntax Ids ::= List{#Id,","}
  syntax Exps ::= List{Exp,","}
  syntax Stmt ::= function #Id ( Ids ) { Stmt }
//@4.7                | return Exp ;
                | Exp ;
  syntax Exp ::= call #Id ( Exps )
//4.6
  syntax Stmt ::= #Id := Exp ; [prec 80 strict(2)]
//4.7
                | return Exp ; [strict]
//5.1
                | spawn #Id ( Exps ) ; [strict(2)]
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
    <k> write(S:#String) ; => . ...</k> 
    <out>... . => ListItem(S) </out>

//2
  rule 
    St1:Stmt St2:Stmt => St1 ~> St2

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
    <k> var X:#Id; => . ...</k> 
    <env>... .Map => X |-> "" ...</env>

//3.3
  rule 
    <k> X:#Id := S:#String; => . ...</k>
    <env>... X |-> (_ => S) ...</env>   

//3.6
  syntax KResult ::= Val

//4
  rule
    <k> X:#Id => K:K ...</k>
    <env>... X |-> K ...</env>

//4.2
/*@4.3
  configuration
    <k> $PGM:K </k> 
    <env> .Map </env> 
    <out> .List </out>
    <procs> .Map </procs>
*/

  rule 
    <k> function X:#Id(Xs:Ids) { St:Stmt } => . ...</k>
    <procs>... . => X |-> (bindTo(Xs) ~> St) ...</procs>

  syntax K ::= bindTo ( Ids )

//4.3
  configuration
    <k> $PGM:K </k> 
    <env> .Map </env> 
    <out> .List </out>
    <procs> .Map </procs>
    <fstack> .List </fstack>

  rule 
    <k> call X:#Id(Vs:Vals) ~> K => Vs ~> Fn ~> return ""; </k>
    <env> Env:Map => . </env>
    <procs>... X |-> Fn:K ...</procs>
    <fstack>... . => frame(K,Env) </fstack>

  syntax ListItem ::= frame ( K , Map )
  syntax Vals ::= List{Val,","}

//4.4
  rule 
    <k> (V:Val,Vs:Vals => Vs) ~> bindTo(X:#Id,Xs:Ids => Xs) ...</k>
    <env>... . => X |-> V ...</env>

//4.5
  rule .Vals ~> bindTo(.Ids) => .

//5
  rule 
    <k> return V:Val ; ~> _ => V ~> K </k>
    <env> _ => Env </env>
    <fstack>... frame(K:K, Env:Map) => . </fstack>

/*
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
*/
end module

