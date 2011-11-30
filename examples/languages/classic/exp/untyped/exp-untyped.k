
module EXP-UNTYPED-SYNTAX
  syntax Exp ::= #Int | #Bool | #Id
               | Exp "+" Exp                [strict prec 33 gather(E e)]
               | Exp "-" Exp                [strict prec 33 gather(E e)]
               | Exp "*" Exp                [strict prec 31 gather(E e)]
               | Exp "/" Exp                [strict prec 31 gather(E e)]
               | Exp "%" Exp                [strict prec 31 gather(E e)]
               | "-" Exp                    [strict]
               | Exp "<" Exp                [strict prec 37]
               | Exp "<=" Exp               [strict prec 37]
               | Exp ">" Exp                [strict prec 37]
               | Exp ">=" Exp               [strict prec 37]
               | Exp "==" Exp               [strict prec 37]
               | Exp "!=" Exp               [strict prec 37]
               | Exp "and" Exp              [strict prec 55 gather(E e)]
               | Exp "or" Exp               [strict prec 59 gather(E e)]
               | "not" Exp                  [strict prec 53]
               | "lambda" #Id "." Exp       [latex "\lambda{#1}.{#2}"]
               | "mu" #Id "." Exp           [latex "\mu{#1}.{#2}"]
               | Exp Exp                    [strict prec 10 gather(E e)]
               | "let" #Id "=" Exp "in" Exp
               | "letrec" #Id #Id "=" Exp in Exp
               | "if" Exp "then" Exp "else" Exp [strict(1)]

  macro let X:#Id = E:Exp in E':Exp = (lambda X . E') E
  macro (letrec F:#Id X = E in E') = (let F = mu F . (lambda X . E) in E')
end module

module EXP-UNTYPED
  imports EXP-UNTYPED-SYNTAX

  syntax Val ::= #Int | #Bool
  syntax Exp ::= Val
  syntax KResult ::= Val

  configuration <T color="yellow">
                  <k color="green"> $PGM:Exp </k>
                     <env color="LightSkyBlue"> .Map </env>
                     <store color="white"> .Map </store>
                     <nextLoc color="gray"> 0 </nextLoc>
                </T>

  rule <k> X:#Id => E:Exp ...</k>
       <env>... X |-> L:#Nat ...</env>
       <store>... L |-> E ...</store>
  rule I1:#Int + I2:#Int => I1 +Int I2
  rule _-_(I1,I2) => _-Int_(I1,I2)
  rule I1 * I2 => I1 *Int I2
  rule I1 / I2 => I1 /Int I2 if I2 =/=Bool 0
  rule I1 % I2 => I1 %Int I2 if I2 =/=Bool 0
  rule - I:#Int => -Int I
  rule I1 < I2 => I1 <Int I2
  rule I1 <= I2 => I1 <=Int I2
  rule I1 > I2 => I1 >Int I2
  rule I1 >= I2 => I1 >=Int I2
  rule V1:Val == V2:Val => V1 ==Bool V2
  rule V1 != V2 => V1 =/=Bool V2
  rule T1:#Bool and T2:#Bool => T1 andBool T2
  rule T1 or T2 => T1 orBool T2
  rule not(T:#Bool) => notBool(T)
  rule if  true then E else  _  => E
  rule if false then  _  else E => E

  syntax Val ::= "closure-lambda" "(" Map "," #Id "," Exp ")"
                   [:latex "\textsf{closure}_\lambda({#1},{#2},{#3})":]
  rule <k> lambda X . E => closure-lambda(Env:Map,X,E) ...</k>
       <env> Env </env>
  rule <k> closure-lambda(Env,X,E) V:Val => E ~> env(Env') ...</k>
       <env> Env':Map =>  Env[L/X] </env>
       <store_> . => L|->V <_/store>
       <nextLoc> L => L +Nat 1 </nextLoc>

  syntax Exp ::= "closure-mu" "(" Map "," Exp ")"
                   [:latex "\textsf{closure}_\mu({#1},{#2})":]
  rule <k> mu X . E => closure-mu(Env[L/X],E) ...</k>
       <env> Env </env>
       <store>... . => L |-> closure-mu(Env[L/X],E) ...</store>
       <nextLoc> L => sNat L </nextLoc>
  rule <k> closure-mu(Env,E) => E ~> env(Env') ...</k>
       <env> Env' => Env </env>

***(
// we really need mu closures ...
// the rule below is wrong, because the free variables
// of E can be captured ... nastily ... argh
  rule <k> mu X . E => E ~> env(Env) ...</k>
       <env> Env => Env[L/X] </env>
       <store_> . => L |-> mu X . E <_/store>
       <nextLoc> L => L +Nat 1 </nextLoc> 
***)

// Auxilliary declarations and operations
// Environment recovery
  syntax K ::= "env" "(" Map ")"
  rule <k> V ~> (env(Env) => .) ...</k> <env> _ => Env </env>  [:structural:]
// Tail recursion
  rule (env(_) => .) ~> env(_)                                 [:structural:]
end module
