// Copyright (c) 2013-2018 K Team. All Rights Reserved.
require "substitution.k"
//require "modules/pattern-matching.k"

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

module FUN-UNTYPED-COMMON
  imports DOMAINS-SYNTAX

//@ \subsection{The Syntactic Constructs}

  syntax Name
  syntax Names ::= List{Name,","}

  syntax Exp ::= Int | Bool | String | Name
               | "(" Exp ")"                       [bracket]
  syntax Exps  ::= List{Exp,","}                   [strict]
  syntax Val
  syntax Vals ::= List{Val,","}

  syntax Exp ::= left:
                 Exp "*" Exp                       [strict, arith]
               | Exp "/" Exp                       [strict, arith]
               | Exp "%" Exp                       [strict, arith]
               > left:
                 Exp "+" Exp                       [strict, left, arith]
               | Exp "^" Exp                       [strict, left, arith]
               | Exp "-" Exp                       [strict, prefer, arith]
               | "-" Exp                           [strict, arith]
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
  syntax Val ::= "[" Vals "]"

  syntax ConstructorName
  syntax Exp ::= ConstructorName
               | ConstructorName "(" Exps ")"      [prefer, strict(2)]
  syntax Val ::= ConstructorName "(" Vals ")"

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
  syntax Name ::= "throw" [token]

  syntax Exp ::= "datatype" Type "=" TypeCases Exp

  syntax TypeVar
  syntax TypeVars ::= List{TypeVar,","}

  syntax TypeName
  syntax Type ::= "int" | "bool" | "string"
                | Type "-->" Type                            [right]
                | "(" Type ")"                             [bracket]
                | TypeVar
                | TypeName             [klabel(TypeName), avoid]
                | Type TypeName   [klabel(Type-TypeName), onlyLabel]
                | "(" Types ")" TypeName                    [prefer]
  syntax Types ::= List{Type,","}
  syntax Types ::= TypeVars

  syntax TypeCase ::= ConstructorName
                    | ConstructorName "(" Types ")"
  syntax TypeCases ::= List{TypeCase,"|"}     [klabel(_|TypeCase_)]


//@ \subsection{Additional Priorities}

  syntax priorities @__FUN-UNTYPED-COMMON
                  > ___FUN-UNTYPED-COMMON
                  > arith
                  > _:=__FUN-UNTYPED-COMMON
                  > let_in__FUN-UNTYPED-COMMON
                    letrec_in__FUN-UNTYPED-COMMON
                    if_then_else__FUN-UNTYPED-COMMON
                  > _;__FUN-UNTYPED-COMMON
                  > fun__FUN-UNTYPED-COMMON
                  > datatype_=___FUN-UNTYPED-COMMON
endmodule

module FUN-UNTYPED-MACROS
  imports FUN-UNTYPED-COMMON

//@ \subsection{Desugaring macros}

  rule P1 P2 -> E => P1 -> fun P2 -> E                       [macro]
  rule F P = E => F = fun P -> E                             [macro]

  rule [E1,E2,Es:Exps|T] => [E1|[E2,Es|T]]                   [macro]

//  rule 'TypeName(Tn:TypeName) => (.TypeVars) Tn              [macro]
  rule Type-TypeName(T:Type, Tn:TypeName) => (T) Tn          [macro]

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


module FUN-UNTYPED-SYNTAX
  imports FUN-UNTYPED-COMMON
  imports BUILTIN-ID-TOKENS

  syntax Name ::= r"[a-z][_a-zA-Z0-9]*"            [autoReject, token, prec(2)]
                | #LowerId                         [autoReject, token]
  syntax ConstructorName ::= #UpperId              [autoReject, token]
  syntax TypeVar  ::= r"['][a-z][_a-zA-Z0-9]*"     [autoReject, token]
  syntax TypeName ::= Name                         [autoReject, token]
endmodule


//@ \section{Semantics}

module FUN-UNTYPED
  imports FUN-UNTYPED-COMMON
  imports FUN-UNTYPED-MACROS
  imports DOMAINS
  imports SUBSTITUTION
  //imports PATTERN-MATCHING

  configuration <T color="yellow">
                  <k color="green"> $PGM:Exp </k>
                  <store color="white"> .Map </store>
                </T>

//@ Both Name and functions are values now:

  syntax Val ::= Int | Bool | String | Name
  syntax Exp ::= Val
  syntax Exps ::= Vals
  syntax KResult ::= Val
  syntax Exps ::= Names
  syntax Vals ::= Names

  rule I1 * I2 => I1 *Int I2
  rule I1 / I2 => I1 /Int I2 when I2 =/=K 0
  rule I1 % I2 => I1 %Int I2 when I2 =/=K 0
  rule I1 + I2 => I1 +Int I2
  rule S1 ^ S2 => S1 +String S2
  rule I1 - I2 => I1 -Int I2
  rule - I => 0 -Int I
  rule I1 < I2 => I1 <Int I2
  rule I1 <= I2 => I1 <=Int I2
  rule I1 > I2 => I1 >Int I2
  rule I1 >= I2 => I1 >=Int I2
  rule V1:Val == V2:Val => V1 ==K V2
  rule V1:Val != V2:Val => V1 =/=K V2
  rule ! T => notBool(T)
  rule true  && E => E
  rule false && _ => false
  rule true  || _ => true
  rule false || E => E

  rule if  true then E else _ => E
  rule if false then _ else E => E

  rule isVal(cons) => true
  rule isVal(cons V:Val) => true
  rule cons V:Val [Vs:Vals] => [V,Vs]

  syntax Val ::= ConstructorName

  rule isVal(fun _) => true
  syntax KVariable ::= Name
  syntax Name ::= freshName(Int)    [freshGenerator, function]
  rule freshName(I:Int) => {#parseToken("Name", "#" +String Int2String(I))}:>Name

  rule (. => getMatching(P, V)) ~> (fun P->_ | _) V:Val
  rule matchResult(M:Map) ~> (fun _->E | _) _ => E[M]
  rule (matchFailure => .) ~> (fun (_->_ | Cs:Cases => Cs)) _
//  rule (fun P->E | _) V:Val => E[getMatching(P,V)]  when isMatching(P,V)
//  rule (fun (P->_ | Cs:Cases => Cs)) V:Val  when notBool isMatching(P,V)

/*@ We can reduce multiple bindings to one list binding, and then
apply the usual desugaring of let into function application.
It is important that the rule below is a macro, so let is eliminated
immediately, otherwise it may interfere in ugly ways with substitution. */

  rule let Bs in E => ((fun [names(Bs)] -> E) [exps(Bs)])    [macro]

/*@ We only give the semantics of one-binding letrec.
Multipe bindings are left as an exercise. */

  // changed because of parsing error
  //rule mu X:Name -> E => E[(mu X -> E) / X]
  rule mu X:Name -> E => E[X |-> (mu X -> E)]
  rule letrec F:Name = E in E' => let F = (mu F -> E) in E'  [macro]

/*@ We cannot have \texttt{\&} anymore, but we can give direct
semantics to \texttt{ref}.  We also have to declare \texttt{ref} to
be a value, so that we will never heat on it. */

//  rule <k> & X => L ...</k>  <env>... X |-> L </env>
  rule isVal(ref) => true
  rule <k> ref V:Val => !L:Int ...</k> <store>... .Map => !L |-> V ...</store>
  rule <k> @ L:Int => V:Val ...</k>  <store>... L |-> V ...</store>
  rule <k> L:Int := V:Val => V ...</k>  <store>... L |-> (_=>V) ...</store>
  rule V:Val; E => E

  syntax Val ::= cc(K)
  rule isVal(callcc) => true
  rule <k> (callcc V:Val => V cc(K)) ~> K </k>
  rule <k> cc(K) V:Val ~> _ => V ~> K </k>


//@ Auxiliary getters

  syntax Names ::= names(Bindings)  [function]
  rule names(.Bindings) => .Names
  rule names(X:Name=_ and Bs) => X,names(Bs)

  syntax Exps ::= exps(Bindings)  [function]
  rule exps(.Bindings) => .Exps
  rule exps(_:Name=E and Bs) => E,exps(Bs)

  /* Extra kore stuff */
  syntax KResult ::= Vals
  syntax Exps ::= Names

  /* Matching */
  syntax MatchResult ::= getMatching(Exp, Val)                      [function]
                       | getMatchingAux(Exps, Vals)                 [function]
                       | mergeMatching(MatchResult, MatchResult)    [function]
                       | matchResult(Map)
                       | "matchFailure"

  rule getMatching(C:ConstructorName(Es:Exps), C(Vs:Vals)) => getMatchingAux(Es, Vs)
  rule getMatching([Es:Exps], [Vs:Vals])                   => getMatchingAux(Es, Vs)
  rule getMatching(C:ConstructorName, C) => matchResult(.Map)
  rule getMatching(B:Bool, B)            => matchResult(.Map)
  rule getMatching(I:Int, I)             => matchResult(.Map)
  rule getMatching(S:String, S)          => matchResult(.Map)
  rule getMatching(N:Name, V:Val) => matchResult(N |-> V)
  rule getMatching(_, _) => matchFailure        [owise]

  rule getMatchingAux((E:Exp, Es:Exps), (V:Val, Vs:Vals)) => mergeMatching(getMatching(E, V), getMatchingAux(Es, Vs))
  rule getMatchingAux(.Exps, .Vals)                       => matchResult(.Map)
  rule getMatchingAux(_, _) => matchFailure     [owise]

  rule mergeMatching(matchResult(M1:Map), matchResult(M2:Map)) => matchResult(M1 M2)
    requires intersectSet(keys(M1), keys(M2)) ==K .Set
  //rule mergeMatching(_, _) => matchFailure      [owsie]
  rule mergeMatching(matchResult(_:Map), matchFailure) => matchFailure
  rule mergeMatching(matchFailure, matchResult(_:Map)) => matchFailure
  rule mergeMatching(matchFailure, matchFailure)       => matchFailure

/*@ Besides the generic decomposition rules for patterns and values,
we also want to allow \texttt{[head|tail]} matching for lists, so we add
the following custom pattern decomposition rule: */

  rule getMatching([H:Exp | T:Exp], [V:Val, Vs:Vals])
    => getMatchingAux((H, T), (V, [Vs]))
endmodule
