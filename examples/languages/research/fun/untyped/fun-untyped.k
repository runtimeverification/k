---------------------------------
--- FUN-UNTYPED-SYNTAX module ---
---------------------------------

--- TO DO: Change kmod ... endkm with module ... end module when the reported bug is fixed
kmod FUN-SYNTAX

/*@ \section{Syntax}
As explained above, FUN is an expression language, so every language construct
ends up being an expression construct (directly or indirectly).  We also allow
lists over identifiers and over expressions, like in most of our other languages,
which make FUN more user friendly.  Finally, as seen below, we define a syntax
which is more permissive that it should (that is, the builtin parser of our tool
may parse even incorrect programs as terms of sort \texttt{Exp}).  If one does
not like that, then one can use an external parser or one can define a type
checker/inferences (see fun/type-inference).  Note, however, that there is no
way one can define a grammar that parses precisely the well-typed FUN programs,
simply because those programs do not form a context-free language (the
simply-typed $\lambda$-calculus well-typed expressions already do not form a
context-free language).  */

/*@ The first group of expression constructs are the same as those of the SIMPLE
language, so we do not discuss them anymore here. */

  syntax Exp ::= #Int | #Bool
               | #Id
               | Exp "+" Exp                [:strict prec(33) gather(E e):]
               | Exp "-" Exp                [:strict prec(33) gather(E e):]
               | Exp "*" Exp                [:strict prec(31) gather(E e):]
               | Exp "/" Exp                [:strict prec(31) gather(E e):]
               | Exp "%" Exp                [:strict prec(31) gather(E e):]
               | "-" Exp                    [:strict:]
               | Exp "<" Exp                [:strict prec(37):]
               | Exp "<=" Exp               [:strict prec(37):]
               | Exp ">" Exp                [:strict prec(37):]
               | Exp ">=" Exp               [:strict prec(37):]
               | Exp "==" Exp               [:strict prec(37):]
               | Exp "!=" Exp               [:strict prec(37):]
               | Exp "and" Exp              [:strict prec(55) gather(E e):]
               | Exp "or" Exp               [:strict prec(59) gather(E e):]
               | "not" Exp                  [:strict prec(53):]

/*@ The next group defines the usual functional constructs, namely function
abstraction, function application, let and letrec binders, and conditional.

*/
  syntax Exp ::= "fun" List{Exp} "->" Exp
               | Exp List{Exp}      [:strict prec(10) gather(E e):]
               | List{Exp} "=" List{Exp}    [:prec(53):]   --- Bindings
               | "let" Exp "in" Exp
               | "letrec" Exp "in" Exp
               | "if" Exp "then" Exp "else" Exp [:strict(1):]

               | "[" "]"
               | "[" List{Exp} "]"            [:strict hybrid prec(0):]
               | "car" Exp                  [:strict prec(0):]
               | "cdr" Exp                  [:strict prec(0):]
               | "null?" Exp                [:strict prec(0):]
               | "cons" Exp Exp             [:strict:]

               | "ref" Exp                  [:strict:]
               | "&" #Id
               | "*" Exp                    [:strict:]
               | Exp ":=" Exp               [:strict:]
               | Exp ";" Exp                [:seqstrict prec(110) gather(e E):]

               | "callcc" Exp               [:strict:]

-----------------------------------------------------------------------------
--- Lists should be eventually builtin; for now, they need to be declared ---
-----------------------------------------------------------------------------
--- List{Id}
  syntax List{Id} ::= #Id
                    | "(" ")"
                    | List{Id} "," List{Id} [:strict hybrid assoc id(`(`)) prec(70):]

--- List{Exp}
  syntax List{Exp} ::= Exp | List{Id} | List{Exp} "," List{Exp} [:ditto:]
-----------------------------------------------------------------------------

  macro fun E1:Exp E2:Exp -> E:Exp = fun E1 -> fun E2 -> E
  macro (E1 El:List{Exp} = E2) = (E1 = fun El -> E2)
  macro (Xl1:List{Id} = El1:List{Exp}) and (Xl2:List{Id} = El2:List{Exp}) = ((Xl1,Xl2) = (El1,El2))
  macro [] = [()]
endkm

module FUN-UNTYPED imports FUN-SYNTAX
  syntax Val ::= #Int | #Bool
  syntax Exp ::= Val
  syntax K ::= List{Exp}
  syntax KResult ::= List{Val}

  configuration <T>  <k> .K </k>
                     <env> .Map </env>
                     <store> .Map </store>
                     <nextLoc> 0 </nextLoc>
                </T>

  rule <k> X:#Id => V:Val ...</k> <env>... X|->L:#Nat ...</env> <store>... L|->V ...</store>
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
  syntax Val ::= closure ( Map , List{Id} , Exp )
  rule <k> fun Xl:List{Id} -> E:Exp => closure(Env:Map,Xl,E) ...</k> <env> Env </env> 
  rule <k> closure(Env,Xl,E) Vl:List{Val} => Vl ~> bindTo(Xl) ~> E ~> env(Env') ...</k> <env> Env':Map => Env </env>
  rule <k> let Xl = El:List{Exp} in E => El ~> bindTo(Xl) ~> E ~> env(Env) ...</k> <env> Env </env>
  rule <k> letrec Xl = El in E => bindTo(Xl) ~> El ~> writeTo(Xl) ~> E ~> env(Env) ...</k> <env> Env </env>
  syntax Val ::= cc ( Map , K )
  rule <k> (callcc V => V cc(Env,K)) ~> K </k> <env> Env </env> 
  rule <k> cc(Env,K:K) V ~> _ => V ~> K </k> <env> _ => Env </env> 
  rule if  true then E else _ => E
  rule if false then _ else E => E 
  rule car [V,_:List{Val}] => V
  rule cdr [_:Val,Vl] => [Vl]
  rule null? [()] => true
  rule null? [_:Val,_:List{Val}] => false
  rule cons V [Vl] => [V,Vl]
  rule <k> ref V => L ...</k> <store>... . => L|->V ...</store> <nextLoc> L => sNat L </nextLoc>
  rule <k> &X => L ...</k> <env>... X|->L ...</env>
  rule <k> *L => V ...</k> <store>... L|->V ...</store>
  rule <k> L:=V => V  ...</k> <store>... L|->(_=>V) ...</store>
  rule V1; V2 => V2

----------------------------------------------
--- Auxilliary declarations and operations ---
----------------------------------------------
--- List{Val}
  syntax List{Val} ::= Val | List{Val} "," List{Val} [:ditto:]
  syntax List{Exp} ::= List{Val}

--- Environment recovery
  syntax K ::= env ( Map )
  rule (env(_) => .) ~> env(_)                                         [:structural:]    --- tail recursion
  rule <k> env(Env) => . ...</k> <env> _ => Env </env>                   [:structural:]
  rule <k> V ~> (env(Env) => .) ...</k> <env> _ => Env </env>            [:structural:]

--- bindTo and writeTo
  syntax K ::= bindTo List{Id} | writeTo List{Id}
  rule <k> () ~> bindTo() => . ...</k>                                   [:structural:]
  rule <k> ((V=>()),_:List{Val}) ~> bindTo((X=>()),_:List{Id}) ...</k>
       <env> Env => Env[N/X] </env>
       <store>... . => N|->V ...</store>
       <nextLoc> N:#Nat => sNat N </nextLoc>  if X =/=Bool ()           [:structural:]

  rule <k> bindTo() => . ...</k>                                         [:structural:]
  rule <k> bindTo((X=>()),_:List{Id}) ...</k>
       <env> Env => Env[N/X] </env>
       <nextLoc> N => sNat N </nextLoc>  if X =/=Bool ()               [:structural:]

  rule <k> () ~> writeTo() => . ...</k>                                  [:structural:]
  rule <k> ((V=>()),_:List{Val}) ~> writeTo((X=>()),_:List{Id}) ...</k>
          <env>... X|->L ...</env> <store>... . => L|->V ...</store>           [:structural:]
end module

