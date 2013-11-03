require "modules/substitution.k"

/*!
\title{FUN --- Untyped}
\author{Grigore Ro\c{s}u and Traian Florin \c{S}erb\u{a}nu\c{t}\u{a}
        (\texttt{\{grosu,tserban2\}@illinois.edu})}
\organization{University of Illinois at Urbana-Champaign}
*/

/*@ \section{Abstract}
...
*/

module FUN-UNTYPED-SYNTAX

  syntax Exp ::= Int | Bool | Id
               | "(" Exp ")"             [bracket]
               | Exp Exp                           [strict, left]
               | "&" Id
               | "@" Exp                           [strict]
               | "callcc" Exp                      [strict]
               | "cons" Exp Exp                    [strict]
               > left:
                 Exp "*" Exp                       [strict, left]
               | Exp "/" Exp                       [strict, left]
               | Exp "%" Exp                       [strict, left]
               > left:
                 Exp "+" Exp                       [strict, left]
               | Exp "-" Exp                       [strict, left, prefer]
               > non-assoc:
                 Exp "<" Exp                       [strict, non-assoc]
               | Exp "<=" Exp                      [strict, non-assoc]
               | Exp ">" Exp                       [strict, non-assoc]
               | Exp ">=" Exp                      [strict, non-assoc]
               | Exp "==" Exp                      [strict, non-assoc]
               | Exp "!=" Exp                      [strict, non-assoc]
               > "!" Exp                           [strict]
               > left:
                 Exp "&&" Exp                      [strict(1), left]
               | Exp "||" Exp                      [strict(1), left]
               > Exp ":=" Exp                      [strict]
               > "let" Bindings "in" Exp
               | "letrec" Bindings "in" Exp        [prefer]
               | "if" Exp "then" Exp "else" Exp    [strict(1)]
               | "try" Exp "catch" "(" Id ")" Exp
               > Exp ";" Exp                       [strict(1), right]
               > "fun" Cases
               | "{" Exps "}"          [strict]  // tuple
               | "[" Exps "]"          [strict]  // lists
               | "[" Exps "|" Exp "]"            // list [head|tail] pattern

  syntax Exps ::= List{Exp,","}        [strict]
  syntax Ids  ::= List{Id,","}

  syntax Case  ::= Exp "->" Exp  [binder]
  syntax Cases ::= List{Case, "|"}

  syntax Binding  ::= Exp "=" Exp
  syntax Bindings ::= List{Binding,"and"}

  rule P1 P2 -> E => P1 -> fun P2 -> E                       [macro]
  rule F P = E => F = fun P -> E                             [macro]

  rule [E:Exp,Es|T] => [E|[Es|T]]  when Es =/=K .Exps        [macro]

  syntax Id ::= "head" | "tail" | "null?" | "ref" | "throw"
  syntax Id ::= "$h" | "$t" | "$l" | "$x" | "$k" | "$v"
  rule head => fun [$h|$t] -> $h                             [macro]
  rule tail => fun [$h|$t] -> $t                             [macro]
  rule null? => fun [.Exps] -> true | [$h|$t] -> false       [macro]

//  rule ref => fun $x -> & $x                                 [macro]

  rule try E catch(X) E'
    => callcc (fun $k -> (fun throw -> E)
                         (fun X -> $k E'))  [macro]

  syntax Exp ::= "mu" Case
endmodule


module FUN-UNTYPED
  imports FUN-UNTYPED-SYNTAX
  imports SUBSTITUTION

  configuration <T color="yellow"> 
                  <k color="green"> $PGM:Exp </k>
                  <store color="white"> .Map </store>
                </T>

//@ fun is a Val; Id is Val

  syntax Val ::= Id | Int | Bool | "fun" Cases
  syntax Vals ::= List{Val,","}
  syntax Exp ::= Val
  syntax KResult ::= Val

  rule I1:Int + I2:Int => I1 +Int I2
  rule (I1:Int - I2:Int) => I1 -Int I2
  rule I1:Int * I2:Int => I1 *Int I2
  rule I1:Int / I2:Int => I1 /Int I2 when I2 =/=K 0
  rule I1:Int % I2:Int => I1 %Int I2 when I2 =/=K 0
  rule I1:Int < I2:Int => I1 <Int I2
  rule I1:Int <= I2:Int => I1 <=Int I2
  rule I1:Int > I2:Int => I1 >Int I2
  rule I1:Int >= I2:Int => I1 >=Int I2
  rule V1:Val == V2:Val => V1 ==K V2
  rule V1:Val != V2:Val => V1 =/=K V2
  rule ! T:Bool => notBool(T)
  rule true  && E => E
  rule false && _ => false
  rule true  || _ => true
  rule false || E => E

  rule (fun P->E | _) V:Val => E[getMatching(P,V)]  when isMatching(P,V)
  rule (fun (P->_ | Cs:Cases => Cs)) V:Val  when notBool isMatching(P,V)

  rule decomposeMatching(([H:Exp|T:Exp] => H,T),([V:Val,Vs:Vals] => V,[Vs]))

//  rule let Bs in E => (E[getMatching(ids(Bs),exps(Bs))])

  rule let Bs in E => (fun {ids(Bs)} -> E) {exps(Bs)}

  syntax Exp ::= "mu" Case
  rule mu X:Id -> E:Exp => E[(mu X -> E) / X]
  rule letrec F:Id = E in E' => let F = (mu F -> E) in E'  [macro]

//  rule letrec Bs in E => (fun {ids(Bs)} -> E) (mu {ids(Bs)} -> {exps(Bs)})
//  syntax Exp ::= "mu" Cases
//  rule mu P -> E => E[]
//
//MU: mu F1 = E1 and F2 = E2
//
//MU = {E1[pj1(MU)/F1] , E2[pj2(MU)/F2]}
//
//mu F = E and Bs


//  rule <k> letrec Bs in E
//        => bind(ids(Bs)) ~> assignTo(ids(Bs),exps(Bs)) ~> E ~> env(Rho)...</k>
//       <env> Rho </env>

  rule if  true then E else _ => E
  rule if false then _ else E => E

  syntax Val ::= "{" Vals "}"
               | "[" Vals "]"

  rule cons V:Val [Vs:Vals] => [V,Vs]

//  rule <k> & X => L ...</k>  <env>... X |-> L </env>

  rule <k> ref V:Val => L ...</k> <store>... . => L |-> V ...</store>
  when fresh(L:Int)
  rule <k> @ L:Int => V:Val ...</k>  <store>... L |-> V ...</store>
  rule <k> L:Int := V:Val => V ...</k>  <store>... L |-> (_=>V) ...</store>

  rule V:Val; E => E

  syntax Val ::= cc(K)
  rule <k> (callcc V:Val => V cc(K)) ~> K </k>
  rule <k> cc(K) V:Val ~> _ => V ~> K </k>


/*
  syntax K ::= bindTo(Ids,Exps)         [strict(2)]
             | bindTo(Map)
             | bind(Ids)

  rule bindTo(Xs:Ids,Vs:Vals) => bindTo(getMatching(Xs,Vs))

  rule bindTo(.Map) => .  [structural]
  rule <k> bindTo((X:Id |-> V:Val => .) _) ...</k>
       <env> Rho => Rho[L/X] </env>
       <store>... . => L |-> V ...</store>
    when fresh(L:Int)  [structural]

  rule bind(.Ids) => .                  [structural]
  rule <k> bind(X:Id,Xs => Xs) ...</k>
       <env> Rho => Rho[L/X] </env>
    when fresh(L:Int)                   [structural]

  syntax K ::= assignTo(Ids,Exps)  [strict(2)]

  rule <k> assignTo(.Ids,.Vals) => . ...</k>            [structural]
  rule <k> assignTo((X:Id,Xs => Xs),(V:Val,Vs => Vs)) ...</k>
       <env>... X |-> L ...</env>
       <store>... . => L |-> V ...</store>              [structural]
*/

  syntax Ids ::= ids(Bindings)  [function]
  rule ids(.Bindings) => .Ids
  rule ids(X:Id=_ and Bs) => X,ids(Bs)

  syntax Exps ::= exps(Bindings)  [function]
  rule exps(.Bindings) => .Exps
  rule exps(_:Id=E and Bs) => E,exps(Bs)

endmodule
