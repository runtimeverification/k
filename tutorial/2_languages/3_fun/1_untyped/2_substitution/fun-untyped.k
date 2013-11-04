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

  syntax            Name ::= Token{[a-z][\_a-zA-Z0-9]*}      [notInRules]
  syntax ConstructorName ::= Token{[A-Z][a-zA-Z0-9]*}        [notInRules]

  syntax Exp ::= Int | Bool | String | Name
               | "(" Exp ")"                       [bracket]
               | Exp Exp                           [strict, left]
               | "&" Name
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
               | "try" Exp "catch" "(" Name ")" Exp
               > Exp ";" Exp                       [strict(1), right]
               > "fun" Cases
               | "[" Exps "]"          [strict]
               | "[" Exps "|" Exp "]"

  syntax Exp ::= ConstructorName
               | ConstructorName "(" Exps ")"      [prefer, strict(2)]

  syntax Exps ::= List{Exp,","}        [strict]
  syntax Names  ::= List{Name,","}

  syntax Case  ::= Exp "->" Exp  [binder]
  syntax Cases ::= List{Case, "|"}

  syntax Binding  ::= Exp "=" Exp
  syntax Bindings ::= List{Binding,"and"}

  rule P1 P2 -> E => P1 -> fun P2 -> E                       [macro]
  rule F P = E => F = fun P -> E                             [macro]

  rule [E:Exp,Es|T] => [E|[Es|T]]  when Es =/=K .Exps        [macro]

  syntax Name ::= "head" | "tail" | "null?" | "ref" | "throw"
  syntax Name ::= "$h" | "$t" | "$l" | "$x" | "$k" | "$v"
  rule head => fun [$h|$t] -> $h                             [macro]
  rule tail => fun [$h|$t] -> $t                             [macro]
  rule null? => fun [.Exps] -> true | [$h|$t] -> false       [macro]

//  rule ref => fun $x -> & $x                                 [macro]

  rule try E catch(X) E'
    => callcc (fun $k -> (fun throw -> E)
                         (fun X -> $k E'))  [macro]

/*@ We put the mu here in the syntax module, instead of only in the
semantics as a means to define letrec, so that we can also use it
in programs.
This is particularly useful when testing the definition against
programs, because it allows us to test mu as well. */

  syntax Exp ::= "mu" Case

endmodule


module FUN-UNTYPED
  imports FUN-UNTYPED-SYNTAX
  imports SUBSTITUTION

  configuration <T color="yellow"> 
                  <k color="green"> $PGM:Exp </k>
                  <store color="white"> .Map </store>
                </T>

//@ Both Name and functions are values now:

  syntax Val ::= Name | Int | Bool | String | "fun" Cases
  syntax Vals ::= List{Val,","}
  syntax Exp ::= Val
  syntax KResult ::= Val

  rule I1:Int + I2:Int => I1 +Int I2
  rule S1:String + S2:String => S1 +String S2
  rule I1:Int - I2:Int => I1 -Int I2
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

  syntax Variable ::= Name
  syntax Val ::= ConstructorName
               | ConstructorName "(" Vals ")"

  rule (fun P->E | _) V:Val => E[getMatching(P,V)]  when isMatching(P,V)
  rule (fun (P->_ | Cs:Cases => Cs)) V:Val  when notBool isMatching(P,V)

  rule decomposeMatching(([H:Exp|T:Exp] => H,T),([V:Val,Vs:Vals] => V,[Vs]))

/*@ We can reduce multiple bindings to one list binding, and then
apply the usual desugaring of let into function application. */

  rule let Bs in E => ((fun [names(Bs)] -> E) [exps(Bs)])

/*@ We only give the semantics of one-binding letrec.
Multipe bindings are left as an exercise. */

  syntax Exp ::= "mu" Case
  rule mu X:Name -> E => E[(mu X -> E) / X]
  rule letrec F:Name = E in E' => let F = (mu F -> E) in E'  [macro]

  rule if  true then E else _ => E
  rule if false then _ else E => E

  syntax Val ::= "[" Vals "]"
  rule cons V:Val [Vs:Vals] => [V,Vs]

/*@ We cannot have \texttt{\&} anymore, but we can give direct
semantics to \texttt{ref}: */

//  rule <k> & X => L ...</k>  <env>... X |-> L </env>
  rule <k> ref V:Val => L ...</k> <store>... . => L |-> V ...</store>
  when fresh(L:Int)
  rule <k> @ L:Int => V:Val ...</k>  <store>... L |-> V ...</store>
  rule <k> L:Int := V:Val => V ...</k>  <store>... L |-> (_=>V) ...</store>

  rule V:Val; E => E

  syntax Val ::= cc(K)
  rule <k> (callcc V:Val => V cc(K)) ~> K </k>
  rule <k> cc(K) V:Val ~> _ => V ~> K </k>


//@ Auxiliary getters

  syntax Names ::= names(Bindings)  [function]
  rule names(.Bindings) => .Names
  rule names(X:Name=_ and Bs) => X,names(Bs)

  syntax Exps ::= exps(Bindings)  [function]
  rule exps(.Bindings) => .Exps
  rule exps(_:Name=E and Bs) => E,exps(Bs)

endmodule
