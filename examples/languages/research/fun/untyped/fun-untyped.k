
module FUN-UNTYPED-SYNTAX

  syntax Exp ::= #Int | #Bool | #String | #Id
               | Exp "+" Exp           [:strict prec(33) gather(E e):]
               | Exp "-" Exp           [:strict prec(33) gather(E e):]
               | Exp "*" Exp           [:strict prec(31) gather(E e):]
               | Exp "/" Exp           [:strict prec(31) gather(E e):]
               | Exp "%" Exp           [:strict prec(31) gather(E e):]
               | "-" Exp               [:strict:]
               | Exp "<" Exp           [:strict prec(37):]
               | Exp "<=" Exp          [:strict prec(37):]
               | Exp ">" Exp           [:strict prec(37):]
               | Exp ">=" Exp          [:strict prec(37):]
               | Exp "==" Exp          [:strict prec(37):]
               | Exp "!=" Exp          [:strict prec(37):]
               | Exp "and" Exp         [:strict prec(55) gather(E e):]
               | Exp "or" Exp          [:strict prec(59) gather(E e):]
               | "not" Exp             [:strict prec(53):]

  syntax Exp ::= "fun" Exps "->" Exp
               | Exp Exps               [:strict prec(10) gather(E e):]
               | Exps "=" Exps           [:prec(53):]   --- Bindings
               | "let" Exp "in" Exp
               | "letrec" Exp "in" Exp
               | "if" Exp
                 "then" Exp
                 "else" Exp            [:strict(1):]
// Tuples
---               | "<" Exps ">"          [:strict hybrid prec(0):]
// Lists
               | "[" Exps "]"          [:strict hybrid prec(0):]
               | "car" Exp             [:strict prec(0):]
               | "cdr" Exp             [:strict prec(0):]
               | "null?" Exp           [:strict prec(0):]
               | "cons" Exp Exp        [:strict:]
// References
               | "ref" Exp             [:strict:]
               | "&" #Id
               | "*" Exp               [:strict:]
               | Exp ":=" Exp          [:strict:]
               | Exp ";" Exp           [:seqstrict prec(110) gather(e E):]
// Callcc
               | "callcc" Exp          [:strict:]

  syntax Ids  ::= List{#Id,","}
  syntax Exps ::= List{Exp,","}

  syntax Exps ::= "(" ")"
  macro () = .Exps

  macro fun E1:Exp E2:Exp -> E:Exp = fun E1 -> fun E2 -> E
  macro (E1:Exp Es:Exps = E) = (E1 = fun Es -> E)
  macro (X:#Id = E:Exp) and (Xs:Ids = Es:Exps)
      = ((X,Xs) = (E,Es))
end module


module FUN-UNTYPED
  imports FUN-UNTYPED-SYNTAX
  syntax Val ::= #Int | #Bool
  syntax Vals ::= List{Val,","}
  syntax Exp ::= Val
  syntax KResult ::= Val

//@ \subsection{Configuration}

  configuration <T>  <k color="green"> $PGM:Exp </k>
                     <env color="violet"> .Map </env>
                     <store color="white"> .Map </store>
                     <nextLoc color="gray"> 0 </nextLoc>
                </T>

//@ \subsection{Lookup}

  rule <k> X:#Id => V:Val ...</k>
       <env>... X |-> L:#Nat ...</env>
       <store>... L |-> V ...</store>

//@ \subsection{Arithmetic expressions}

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

//@ \subsection{Functions and Closures}

  syntax Val ::= "closure" "(" Map "," Ids "," Exp ")"
  rule <k> fun Xs:Ids -> E:Exp => closure(Rho:Map,Xs,E) ...</k>
       <env> Rho </env>
  rule <k> closure(Rho,Xs,E) Vs:Vals
        => bindTo(Xs,Vs) ~> E ~> env(Rho') ...</k>
       <env> Rho':Map => Rho </env>

//@ \subsection{Let}

  rule <k> let Xs = Es:Exps in E
        => bindTo(Xs,Es) ~> E ~> env(Rho) ...</k>
       <env> Rho </env>

//@ \subsection{Letrec}

  rule <k> letrec Xs = Es:Exps in E
        => bind(Xs) ~> assignTo(Xs,Es) ~> E ~> env(Rho) ...</k>
       <env> Rho </env>

//@ \subsection{Callcc}

  syntax Val ::= "cc" "(" Map "," K ")"
  rule <k> (callcc V => V cc(Rho,K)) ~> K </k> <env> Rho </env> 
  rule <k> cc(Rho,K:K) V ~> _ => V ~> K </k> <env> _ => Rho </env> 

//@ \subsection{Conditional}

  rule if  true then E else _ => E
  rule if false then _ else E => E 

//@ \subsection{Lists}

  rule car [V,_:Vals] => V
  rule cdr [_:Val,Vs] => [Vs]
  rule null? [] => true
  rule null? [_:Val,_:Vals] => false
  rule cons V [Vs] => [V,Vs]

//@ \subsection{References}

  rule <k> ref V => L ...</k>
       <store>... . => L |-> V ...</store>
       <nextLoc> L => sNat L </nextLoc>
  rule <k> &X => L ...</k> <env>... X|->L ...</env>
  rule <k> *L => V ...</k> <store>... L|->V ...</store>
  rule <k> L:=V => V  ...</k> <store>... L|->(_=>V) ...</store>
  rule V1; V2 => V2


//@ \subsection{Auxilliary operations}

//@ \subsubsection{Environment recovery}

  syntax K ::= "env" "(" Map ")"
  rule (env(_) => .) ~> env(_)            [:structural:]    --- tail recursion
  rule <k> env(Rho) => . ...</k>
       <env> _ => Rho </env>              [:structural:]
  rule <k> V ~> (env(Rho) => .) ...</k>
       <env> _ => Rho </env>              [:structural:]

//@ \subsubsection{bindTo and bind}

  syntax K ::= "bindTo" "(" Ids "," Exps ")"        [:strict(2):]
             | "bind" "(" Ids ")"

  rule <k> bindTo(.Ids,.Vals) => . ...</k>             [:structural:]
  rule <k> bindTo((X,Xs => Xs),(V,Vs => Vs)) ...</k>
       <env> Rho => Rho[N/X] </env>
       <store>... . => N |-> V ...</store>
       <nextLoc> N:#Nat => sNat N </nextLoc>              [:structural:]

  rule <k> bind(.Ids) => . ...</k>                      [:structural:]
  rule <k> bind(X,Xs => Xs) ...</k>
       <env> Rho => Rho[N/X] </env>
       <nextLoc> N => sNat N </nextLoc>                   [:structural:]

//@ \subsubsection{assignTo}

  syntax K ::= "assignTo" "(" Ids "," Exps ")"  [:strict(2):]

  rule <k> assignTo(.Ids,.Vals) => . ...</k>            [:structural:]
  rule <k> assignTo((X,Xs => Xs),(V,Vs => Vs)) ...</k>
       <env>... X |-> L ...</env>
       <store>... . => L |-> V ...</store>                [:structural:]

end module

***(

  syntax Exp ::= try Exp catch ( #Id ) Exp
--- assume that continuation and value are not free in E and E'
  macro try E catch(X:#Id) E':Exp
      = callcc (fun continuation
                -> (fun throw -> E:Exp)
                     (fun value -> continuation ((fun X -> E') value)))

***)
