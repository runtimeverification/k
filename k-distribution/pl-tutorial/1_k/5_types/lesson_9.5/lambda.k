// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

// NOTE: this definition is not up to date with the latest version of K, as it
// uses substitution, unification and symbolic reasoning.
// It is intended for documentation and academic purposes only.

require "unification.k"
require "substitution.md"

module LAMBDA-SYNTAX
  imports DOMAINS-SYNTAX
  imports KVAR
  syntax Exp ::= Int | Bool | KVar
               | "(" Exp ")"                      [bracket]
               | Exp Exp                          [seqstrict, left]
               > Exp "*" Exp                      [seqstrict, left]
               | Exp "/" Exp                      [seqstrict]
               > Exp "+" Exp                      [seqstrict, left]
               > Exp "<=" Exp                     [seqstrict]
               > "lambda" KVar "." Exp
               | "if" Exp "then" Exp "else" Exp   [seqstrict]
               | "let" KVar "=" Exp "in" Exp        [strict(2)]
               | "letrec" KVar KVar "=" Exp "in" Exp [macro]
               | "mu" KVar "." Exp
endmodule

module LAMBDA
  imports LAMBDA-SYNTAX
  imports DOMAINS
  imports UNIFICATION
  imports SUBSTITUTION

  syntax Type ::= "int" | "bool"
                | Type "->" Type                  [klabel(functionType)]
                | "(" Type ")"                    [bracket]

  syntax Exp ::= Type

  syntax KResult ::= Type

  configuration <k color="green"> $PGM:Exp </k>
                <tenv color="red"> .Map </tenv>

  rule _I:Int => int
  rule _B:Bool => bool
  rule <k> X:KVar => T ...</k>  <tenv>... X |-> T:Type ...</tenv>
  rule int * int => int
  rule int / int => int
  rule int + int => int
  rule int <= int => bool

  syntax Exp ::= Exp "->" Exp                  [seqstrict, klabel(functionType)]
  rule <k> lambda X:KVar . E => ?T:Type -> E ~> setTenv(TEnv) ...</k>
       <tenv> TEnv => TEnv[X <- ?T] </tenv>

  rule (T1:Type -> T2:Type) T1 => T2
  rule if bool then T:Type else T => T

  syntax TypeSchema ::= "(" "forall" Set ")" Type
  rule <k> let X = T:Type in E => E ~> setTenv(TEnv) ...</k>
       <tenv> TEnv
        => TEnv[X <- (forall #metaKVariables(T) -Set #metaKVariables(setTenv(TEnv))) T]
       </tenv>
  rule <k> X:KVar => #renameMetaKVariables(T, Tvs) ...</k>
       <tenv>... X |-> (forall Tvs) T ...</tenv>

  rule letrec F X = E in E' => let F = mu F . lambda X . E in E'
  rule <k> mu X:KVar . E:Exp => (?T:Type -> ?T) E ~> setTenv(TEnv) ...</k>
       <tenv> TEnv => TEnv[X <- ?T] </tenv>

  syntax KItem ::= setTenv(Map)
  rule <k> T:Type ~> setTenv(TEnv) => T ...</k>  <tenv> _ => TEnv </tenv>
endmodule
