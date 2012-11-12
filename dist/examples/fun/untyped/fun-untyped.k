module FUN-UNTYPED-SYNTAX

  syntax Id ::= "head" | "tail" | "null?"

  syntax Exp ::= Int | Bool | Id
               | "(" Exp ")"             [bracket]
//               | "-" Exp                 [strict]
               | Exp Exp                 [strict, left]
               | "ref" Exp
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
               > Exp ";" Exp           [seqstrict, right]
               > "fun" Cases

  syntax Exps ::= List{Exp,","}        [strict]
  syntax Ids  ::= List{Id,","}

  syntax Case  ::= Exp "->" Exp
  syntax Cases ::= List{Case, "|"}

  syntax Binding  ::= Exp "=" Exp
  syntax Bindings ::= List{Binding,"and"}

//  syntax Cases ::= Exp "->" Exp
//                 | Cases "|" Cases  [right]
//  syntax Bindings  ::= Exp "=" Exp
//                    | Bindings "and" Bindings  [right]

  rule P1 P2 -> E => P1 -> fun P2 -> E  [macro]
  rule F P = E => F = fun P -> E        [macro]
  rule [E,Es|T] => [E|[Es|T]]  when Es =/=K .Exps  [macro]

// I wish I were able to use just parentheses for tuples ...
// Unfortunately, that gets into parsing ambiguities with (...) for grouping
  syntax Exp ::= "{" Exps "}"          [strict, hybrid]  // tuple
  syntax Exp ::= "[" Exps "]"          [strict, hybrid]
               | "[" Exps "|" Exp "]"

  syntax Id ::= "$h" | "$t" | "$l"
  rule head => fun [$h|$t] -> $h  [macro]
  rule tail => fun [$h|$t] -> $t  [macro]
  rule null? => fun [.Exps] -> true | $l -> false  [macro]
endmodule


module FUN-UNTYPED
  imports FUN-UNTYPED-SYNTAX

  syntax Val ::= Int | Bool
  syntax Vals ::= List{Val,","}
  syntax Exp ::= Val
  syntax KResult ::= Val

rule isVal({_:Vals}) => true

  configuration <T> 
                  <k color="green"> $PGM:Exp </k>
                  <env color="violet"> .Map </env>
                  <store color="white"> .Map </store>
                  <match>
                    <task multiplicity="*">
                      <pattern> .Exps </pattern>
                      <value> .Vals </value>
                    </task>
                    <ids multiplicity="?"> .Ids </ids>
                    <vals multiplicity="?"> .Vals </vals>
                    <exp multiplicity="?"> .K </exp>
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

// initiate matching
  rule <k> match(P -> E | Cases, V) => match(Cases,V) ...</k>
       <match> . => <task> <pattern> P </pattern> <value> V </value> </task>
                 <exp> E </exp> <ids> .Ids </ids> <vals> .Exps </vals> </match>
// success
  rule <k> match(_,_) => bindTo(Xs,Vs) ~> E ...</k>
       <match> <ids> Xs </ids> <vals> Vs </vals> <exp> E </exp> => .  </match>
// generate new tasks
  rule <pattern> P,Ps => Ps </pattern> <value> V,Vs => Vs </value>
       (. => <task> <pattern> P </pattern> <value> V </value> </task>)
// collect terminated tasks 
  rule <task> <pattern> . </pattern> <value> . </value> </task> => .
// case 1: value
  rule <pattern> V:Val => . </pattern> <value> V => . </value> 
// case 2: variable
  rule <pattern> X:Id => . </pattern> <value> V:Val => . </value>
       <ids> Xs => X,Xs </ids> <vals> Vs => V,Vs </vals>
    when notBool(X in Xs)
// case 3: tuple
  rule <pattern> {Ps} => Ps </pattern> <value> {Vs} => Vs </value>
// case 4: list with explicit elements
  rule <pattern> [Ps] => Ps </pattern> <value> [Vs] => Vs </value>
// case 5: list with [head|tail]
  rule <pattern> [P|Ps] => P,Ps </pattern> <value> [V,Vs] => V,[Vs] </value>
// empty match cell when fail: // make sure use kompile -transition="otherwise"
  rule <match> <exp>_</exp> _ => . </match>  [otherwise]

  rule <k> let Bs in E
           => bindTo(getIds(Bs),getExps(Bs))
              ~> E
                 ~> env(Rho) ...</k>
       <env> Rho </env>

  rule <k> rec Bs in E
           => bind(getIds(Bs))
              ~> assignTo(getIds(Bs),getExps(Bs))
                 ~> E
                    ~> env(Rho) ...</k>
       <env> Rho </env>
  
  rule if  true then E else _ => E
  rule if false then _ else E => E



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

  syntax Ids ::= getIds(Bindings)  [function]
  rule getIds(.Bindings) => .Ids
  rule getIds(X:Id=_ and Bs) => X,getIds(Bs)

  syntax Exps ::= getExps(Bindings)  [function]
  rule getExps(.Bindings) => .Exps
  rule getExps(_:Id=E and Bs) => E,getExps(Bs)

  syntax Bool ::= Id "in" Ids  [function]
  rule X:Id in (X,_) => true
  rule X:Id in (Y:Id,Xs => Xs) when X =/=K Y
  rule _:Id in .Ids => false

endmodule
