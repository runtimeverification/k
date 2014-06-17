// Copyright (c) 2013-2014 K Team. All Rights Reserved.
require "modules/substitution.k"

/*!
\title{FUN --- Untyped --- Substitution}
\author{Grigore Ro\c{s}u and Traian Florin \c{S}erb\u{a}nu\c{t}\u{a}
        (\texttt{\{grosu,tserban2\}@illinois.edu})}
\organization{University of Illinois at Urbana-Champaign}
*/

/*@ \section{Abstract}
This is the substitution-based definition of FUN.  For additional
explanations regarding the semantics of the various FUN constructs,
the reader should consult the emvironment-based definition of FUN. */


//@ \section{Syntax}

module FUN-UNTYPED-SYNTAX

//@ \subsection{The Syntactic Constructs}

  syntax Name ::= Token{[a-z][\_a-zA-Z0-9]*}       [notInRules]
  syntax Names ::= List{Name,","}

  syntax Exp ::= Int | Bool | String | Name
               | "(" Exp ")"                       [bracket]
  syntax Exps  ::= List{Exp,","}                   [strict]

  syntax Exp ::= left:
                 Exp "*" Exp                       [strict, arith]
               | Exp "/" Exp                       [strict, arith]
               | Exp "%" Exp                       [strict, arith]
               > left:
                 Exp "+" Exp                       [strict, left, arith]
               | Exp "^" Exp                       [strict, left, arith]
               | Exp "-" Exp                       [strict, prefer, arith]
               > non-assoc:
                 Exp "<" Exp                       [strict, arith]
               | Exp "<=" Exp                      [strict, arith]
               | Exp ">" Exp                       [strict, arith]
               | Exp ">=" Exp                      [strict, arith]
               | Exp "==" Exp                      [strict, arith]
               | Exp "!=" Exp                      [strict, arith]
               > "!" Exp                           [strict, arith]
               > Exp "&&" Exp                      [strict(1), left, arith]
               > Exp "||" Exp                      [strict(1), left, arith]

  syntax Exp ::= "if" Exp "then" Exp "else" Exp    [strict(1)]

  syntax Exp ::= "[" Exps "]"                      [strict]
               | "cons" |  "head" | "tail" | "null?"
               | "[" Exps "|" Exp "]"

  syntax ConstructorName ::= Token{[A-Z][a-zA-Z0-9]*}   [notInRules]
  syntax Exp ::= ConstructorName
               | ConstructorName "(" Exps ")"      [prefer, strict(2)]

  syntax Exp ::= "fun" Cases
               | Exp Exp                           [strict, left]
  syntax Case  ::= Exp "->" Exp                    [binder]
// NOTE: The binder attribute above is the only difference between this
// module and the syntax module of environment-based FUN.  We need
// to fix a bug in order to import modules and override the attributes
// of operations.
  syntax Cases ::= List{Case, "|"}

  syntax Exp ::= "let" Bindings "in" Exp
               | "letrec" Bindings "in" Exp                 [prefer]
  syntax Binding  ::= Exp "=" Exp
  syntax Bindings ::= List{Binding,"and"}

  syntax Exp ::= "ref"
               | "&" Name
               | "@" Exp                           [strict]
               | Exp ":=" Exp                      [strict]
               | Exp ";" Exp                       [strict(1), right]

  syntax Exp ::= "callcc"
               | "try" Exp "catch" "(" Name ")" Exp
  syntax Name ::= "throw"

  syntax Exp ::= "datatype" Type "=" TypeCases Exp

  syntax TypeVar  ::= Token{[\'][a-z][\_a-zA-Z0-9]*}    [notInRules]
  syntax TypeVars ::= List{TypeVar,","}

  syntax TypeName ::= Token{[a-z][\_a-zA-Z0-9]*}        [notInRules]
  syntax Type ::= "int" | "bool" | "string"
                | Type "-->" Type                            [right]
                | "(" Type ")"                             [bracket]
                | TypeVar
                | TypeName            [klabel('TypeName), onlyLabel]
                | Type TypeName  [klabel('Type-TypeName), onlyLabel]
                | "(" Types ")" TypeName                    [prefer]
  syntax Types ::= List{Type,","}

  syntax TypeCase ::= ConstructorName
                    | ConstructorName "(" Types ")"
  syntax TypeCases ::= List{TypeCase,"|"}


//@ \subsection{Additional Priorities}

  syntax priorities '@_
                  > '__
                  > arith
                  > '_:=_
                  > 'let_in_ 'letrec_in_ 'if_then_else_
                  > '_;_
                  > 'fun_
                  > 'datatype_=__


//@ \subsection{Desugaring macros}

  rule P1 P2 -> E => P1 -> fun P2 -> E                       [macro]
  rule F P = E => F = fun P -> E                             [macro]

  rule [E:Exp,Es|T] => [E|[Es|T]]  when Es =/=K .Exps        [macro]

  rule 'TypeName(Tn:TypeName) => (.TypeVars) Tn              [macro]
  rule 'Type-TypeName(T:Type,,Tn:TypeName) => (T) Tn         [macro]

  syntax Name ::= "$h" | "$t"
  rule head => fun [$h|$t] -> $h                             [macro]
  rule tail => fun [$h|$t] -> $t                             [macro]
  rule null? => fun [.Exps] -> true | [$h|$t] -> false       [macro]

  syntax Name ::= "$k" | "$v"
  rule try E catch(X) E'
    => callcc (fun $k -> (fun throw -> E)(fun X -> $k E'))   [macro]

  rule datatype T = TCs E => E                               [macro]

/*@ mu needed for letrec, but we put it here so we can also write
programs with mu in them, which is particularly useful for testing. */

  syntax Exp ::= "mu" Case

endmodule


//@ \section{Semantics}

module FUN-UNTYPED
  imports FUN-UNTYPED-SYNTAX
  imports SUBSTITUTION

  configuration <T color="yellow"> 
                  <k color="green"> $PGM:Exp </k>
                  <store color="white"> .Map </store>
                </T>

//@ Both Name and functions are values now:

  syntax Val ::= Int | Bool | String | Name
  syntax Vals ::= List{Val,","}
  syntax Exp ::= Val
  syntax KResult ::= Val

  rule I1:Int * I2:Int => I1 *Int I2
  rule I1:Int / I2:Int => I1 /Int I2 when I2 =/=K 0
  rule I1:Int % I2:Int => I1 %Int I2 when I2 =/=K 0
  rule I1:Int + I2:Int => I1 +Int I2
  rule S1:String ^ S2:String => S1 +String S2
  rule I1:Int - I2:Int => I1 -Int I2
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

  rule if  true then E else _ => E
  rule if false then _ else E => E

  syntax Val ::= "cons" | "[" Vals "]"
  rule isVal(cons V:Val) => true
  rule cons V:Val [Vs:Vals] => [V,Vs]

  syntax Val ::= ConstructorName
               | ConstructorName "(" Vals ")"

  syntax Val ::= "fun" Cases
  syntax Variable ::= Name
  rule (fun P->E | _) V:Val => E[getMatching(P,V)]  when isMatching(P,V)
  rule (fun (P->_ | Cs:Cases => Cs)) V:Val  when notBool isMatching(P,V)
  rule decomposeMatching(([H:Exp|T:Exp] => H,T),([V:Val,Vs:Vals] => V,[Vs]))

/*@ We can reduce multiple bindings to one list binding, and then
apply the usual desugaring of let into function application. 
It is important that the rule below is a macro, so let is eliminated
immediately, otherwise it may interfere in ugly ways with substitution. */

  rule let Bs in E => ((fun [names(Bs)] -> E) [exps(Bs)])    [macro]

/*@ We only give the semantics of one-binding letrec.
Multipe bindings are left as an exercise. */

  rule mu X:Name -> E => E[(mu X -> E) / X]
  rule letrec F:Name = E in E' => let F = (mu F -> E) in E'  [macro]

/*@ We cannot have \texttt{\&} anymore, but we can give direct
semantics to \texttt{ref}.  We also have to declare \texttt{ref} to
be a value, so that we will never heat on it. */

//  rule <k> & X => L ...</k>  <env>... X |-> L </env>
  syntax Val ::= "ref"
  rule <k> ref V:Val => !L:Int ...</k> <store>... .Map => !L |-> V ...</store>
  rule <k> @ L:Int => V:Val ...</k>  <store>... L |-> V ...</store>
  rule <k> L:Int := V:Val => V ...</k>  <store>... L |-> (_=>V) ...</store>
  rule V:Val; E => E

  syntax Val ::= "callcc" | cc(K)
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
