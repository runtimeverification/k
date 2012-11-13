module FUN-UNTYPED-SYNTAX

  syntax Id ::= "head" | "tail" | "null?" | "ref" | "throw"

  syntax Exp ::= Int | Bool | Id
               | "(" Exp ")"             [bracket]
//               | "-" Exp                 [strict]
               | Exp Exp                 [strict, left]
               | "&" Id
               | "@" Exp                 [strict]
               | "callcc" Exp            [strict]
               | "cons" Exp Exp          [strict]
               > left:
                 Exp "*" Exp             [strict, left]
               | Exp "/" Exp             [strict, left]
               | Exp "%" Exp             [strict, left]
               > left:
                 Exp "+" Exp             [strict, left]
               | Exp "-" Exp             [strict, left]
               > non-assoc:
                 Exp "<" Exp             [strict, non-assoc]
               | Exp "<=" Exp            [strict, non-assoc]
               | Exp ">" Exp             [strict, non-assoc]
               | Exp ">=" Exp            [strict, non-assoc]
               | Exp "==" Exp            [strict, non-assoc]
               | Exp "!=" Exp            [strict, non-assoc]
               > "!" Exp                 [strict]
               > left:
                 Exp "&&" Exp            [strict(1), left]
               | Exp "||" Exp            [strict(1), left]
               > Exp ":=" Exp          [strict]
               > "let" Bindings "in" Exp
// change next to letrec as soon as bug is fixed
               | "rec" Bindings "in" Exp
               | "if" Exp "then" Exp "else" Exp  [strict(1)]
               | "try" Exp "catch" "(" Id ")" Exp
               > Exp ";" Exp           [strict(1), right]
               > "fun" Cases
// I wish I were able to use just parentheses for tuples ...
// Unfortunately, that gets into parsing ambiguities with (...) for grouping
               | "{" Exps "}"          [strict]  // tuple
               | "[" Exps "]"          [strict]  // lists
               | "[" Exps "|" Exp "]"            // list [head|tail] pattern

  syntax Exps ::= List{Exp,","}        [strict]
  syntax Ids  ::= List{Id,","}

  syntax Case  ::= Exp "->" Exp
  syntax Cases ::= List{Case, "|"}

  syntax Binding  ::= Exp "=" Exp
  syntax Bindings ::= List{Binding,"and"}

  rule P1 P2 -> E => P1 -> fun P2 -> E                       [macro]
  rule F P = E => F = fun P -> E                             [macro]
  rule [E:Exp,Es|T] => [E|[Es|T]]  when Es =/=K .Exps        [macro]

  syntax Id ::= "$h" | "$t" | "$l" | "$x" | "$k" | "$v"
  rule head => fun [$h|$t] -> $h                             [macro]
  rule tail => fun [$h|$t] -> $t                             [macro]
  rule null? => fun [.Exps] -> true | [$h|$t] -> false       [macro]
  rule ref => fun $x -> & $x                                 [macro]
  rule try E catch(X) E'
    => callcc (fun $k -> (fun throw -> E)
                         (fun $v -> $k ((fun X -> E') $v)))  [macro]
endmodule


module FUN-UNTYPED
  imports FUN-UNTYPED-SYNTAX

  syntax Val ::= Int | Bool
  syntax Vals ::= List{Val,","}
  syntax Exp ::= Val
  syntax KResult ::= Val

// the "function" tag should not be needed; currently needed due to a tool bug
  rule isVal({_:Vals}) => true  [function]
  rule isVal([_:Vals]) => true  [function]

  configuration <T color="yellow"> 
                  <k color="green"> $PGM:Exp </k>
                  <env color="violet"> .Map </env>
                  <store color="white"> .Map </store>
                  <match color="black">
                    <task color="red" multiplicity="?"> .Bag </task>
                    <then color="blue" multiplicity="?"> .K </then>
                  </match>
                </T>

  rule <k> X:Id => V ...</k>
       <env>... X |-> L ...</env>
       <store>... L |-> V ...</store>

  rule I1:Int + I2:Int => I1 +Int I2
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


  syntax Val ::= closure(Map,Cases)
  rule <k> fun Cases => closure(Rho,Cases) ...</k>
       <env> Rho </env>
  rule <k> closure(Rho,Cases) V:Val => match(Cases,V) ~> env(Rho') ...</k>
       <env> Rho' => Rho </env>

  syntax K ::= match(Cases,Val)

  syntax BagItem ::= Exps "::" Exps

// initiate matching
  rule <k> match((P:Exp -> E:Exp | Cases => Cases), V:Val) ...</k>
       <match> . => <task> P::V </task> <then> bindTo(.Ids,.Vals) ~> E </then>
       </match>
// success
  rule <k> match(_,_) => K ...</k> (<task> . </task> <then> K </then> => .)
// generate new tasks
  rule P:Exp,Ps :: V:Val,Vs => P::V  Ps::Vs  when Ps =/=K .Exps
// collect terminated tasks
  rule .Exps :: .Exps => .
// case 1: value
  rule V:Val :: V => .
// case 2: variable
  rule <task>... X:Id :: V:Val => . ...</task>
       <then> bindTo((Xs => X,Xs),(Vs => V,Vs)) ...</then>
    when notBool(X in Xs)
// case 3: tuple
  rule {Ps:Exps}::{Vs:Vals} => Ps::Vs
// case 4: list with explicit elements
  rule [Ps:Exps]::[Vs:Vals] => Ps::Vs
// case 5: list with [head|tail]
  rule [P:Exp|T:Exp]::[V:Val,Vs:Vals] => P::V  T::[Vs]
// empty match cell when fail: // make sure use kompile -transition="otherwise"
  rule <match> <task>_</task> _ => . </match>  [otherwise]

  rule <k> let Bs in E
        => bindTo(ids(Bs),exps(Bs)) ~> E ~> env(Rho) ...</k>
       <env> Rho </env>

  rule <k> rec Bs in E
        => bind(ids(Bs)) ~> assignTo(ids(Bs),exps(Bs)) ~> E ~> env(Rho)...</k>
       <env> Rho </env>
  
  rule if  true then E else _ => E
  rule if false then _ else E => E

  rule cons V:Val [Vs:Vals] => [V,Vs]

  rule <k> & X => L ...</k>  <env>... X |-> L </env>
  rule <k> @ L => V ...</k>  <store>... L |-> V ...</store>
  rule <k> L := V:Val => V ...</k>  <store>... L |-> (_=>V) ...</store>

  rule _:Val; E => E

  syntax Val ::= cc(Map,K)
  rule <k> (callcc V:Val => V cc(Rho,K)) ~> K </k>  <env> Rho </env>
  rule <k> cc(Rho,K) V:Val ~> _ => V ~> K </k>  <env> _ => Rho </env>


//@ \subsection{Auxiliary operations}

//@ \subsubsection{Environment recovery}

  syntax K ::= env(Map)
  rule (env(_) => .) ~> env(_)  [anywhere]   // tail recursion
  rule <k> _:Val ~> (env(Rho) => .) ...</k> <env> _ => Rho </env>  [structural]

//@ \subsubsection{bindTo and bind}

  syntax K ::= bindTo(Ids,Exps)        [strict(2)]
             | bind(Ids)

  rule bindTo(.Ids,.Vals) => .  [structural]
  rule <k> bindTo((X:Id,Xs => Xs),(V:Val,Vs => Vs)) ...</k>
       <env> Rho => Rho[L/X] </env>
       <store>... . => L |-> V ...</store>
    when fresh(L:Int)  [structural]

  rule bind(.Ids) => .          [structural]
  rule <k> bind(X:Id,Xs => Xs) ...</k>
       <env> Rho => Rho[L/X] </env>
    when fresh(L:Int)  [structural]

//@ \subsubsection{assignTo}

  syntax K ::= assignTo(Ids,Exps)  [strict(2)]

  rule <k> assignTo(.Ids,.Vals) => . ...</k>            [structural]
  rule <k> assignTo((X:Id,Xs => Xs),(V:Val,Vs => Vs)) ...</k>
       <env>... X |-> L ...</env>
       <store>... . => L |-> V ...</store>              [structural]

//@ \subsubsection{getters}

  syntax Ids ::= ids(Bindings)  [function]
  rule ids(.Bindings) => .Ids
  rule ids(X:Id=_ and Bs) => X,ids(Bs)

  syntax Exps ::= exps(Bindings)  [function]
  rule exps(.Bindings) => .Exps
  rule exps(_:Id=E and Bs) => E,exps(Bs)

  syntax Bool ::= Id "in" Ids  [function]
  rule X:Id in (X,_) => true
  rule X:Id in (Y:Id,Xs => Xs) when X =/=K Y
  rule _:Id in .Ids => false

endmodule
