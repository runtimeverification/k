require "modules/unification.k"

module TYPES
  imports UNIFICATION  // this should not be here

  syntax TypeVar ::= "dummy"
  syntax BasicType ::= "int" | "bool"
  syntax Type ::= BasicType
                | Type "->" Type                  [strict]
                | "(" Type ")"                    [bracket]
                | TypeVar
  syntax Types ::= List{Type,","}

  syntax TypeSchema ::= Type
                      | "(" "forall" Types ")" Type
                          [latex((\forall{#1}){#2})]
  syntax TypeSchemas ::= List{TypeSchema,","}

// Free type variables.  These should be generic and builtin, for all binders.

  syntax Types ::= ftv(TypeSchemas)  [function]
  rule ftv(BT:BasicType) => .Types
  rule ftv(Tv:TypeVar) => Tv,.Types
  rule ftv(T1:Type -> T2:Type) => union(ftv(T1),ftv(T2))
  rule ftv((forall Tvs:Types) T:Type) => diff(ftv(T),Tvs)
  rule ftv(.TypeSchemas) => .Types
  rule ftv(TS1:TypeSchema,TS2:TypeSchema,TSs:TypeSchemas)
    => union(ftv(TS1),ftv(TS2,TSs))

// The operations below should be generic and builtin, for all lists

  syntax Types ::= union(Types,Types)  [function]
                 | diff(Types,Types)   [function, latex({#1}-_{\it Types}{#2})]
                 | insert(Type,Types)  [function]
                 | delete(Type,Types)  [function]
  syntax Int ::= "|" Types "|"         [function]
  rule union(.Types,Ts':Types) => Ts'
  rule union((T:Type,Ts:Types),Ts':Types) => union(Ts,insert(T,Ts'))
  rule diff(Ts:Types,.Types) => Ts
  rule diff(Ts:Types,(T:Type,Ts':Types)) => diff(delete(T,Ts),Ts')
  rule insert(T:Type,.Types) => T,.Types
  rule insert(T:Type,(T':Type,Ts:Types))
    => #if T ==K T' #then T',Ts #else T',insert(T,Ts) #fi
  rule delete(T:Type,.Types) => .Types
  rule delete(T:Type,(T':Type,Ts:Types))
    => #if T ==K T' #then Ts #else T',delete(T,Ts) #fi
  rule |T:Type,Ts:Types| => 1 +Int |Ts|
  rule |.Types| => 0

// Type substitution: T[fresh / Tvs]* substitutes fresh types for
// the list of type variables Tvs.

  syntax K  ::= Type "[" "fresh" "/" Types "]*"
  rule T:Type[fresh / .Types]* => T
  rule T:Type[fresh / Tv:Type,Tvs:Types]*
    => substitute(Tv,,F,,T)[fresh / Tvs]*
    when fresh(F:TypeVar)


// Next should probably be generic in some way, for all maps ...
// although note that it does something specific for type schemas.
// This was just a trick, to save us from defining map application on schemas

  syntax Types ::= "types" "(" Map ")"
  rule types(X:Id |-> T:Type TEnv:Map) => T,types(TEnv) [anywhere]
  rule types(X:Id |-> (forall_)T:Type TEnv:Map) => T,types(TEnv) [anywhere]
  rule types(.Map) => .Types [anywhere]
endmodule

module LAMBDA
  imports TYPES
  syntax UnificationVar ::= TypeVar

  syntax Exp ::= Int | Bool | Id
               | "(" Exp ")"                      [bracket]
               | Exp Exp                          [strict, left]
               > Exp "*" Exp                      [strict, left]
               | Exp "/" Exp                      [strict]
               > Exp "+" Exp                      [strict, left]
               > Exp "<=" Exp                     [strict]
               > "lambda" Id "." Exp
               | "if" Exp "then" Exp "else" Exp   [strict]
               | "let" Id "=" Exp "in" Exp        [strict(2)]
               | "letrec" Id Id "=" Exp "in" Exp
               | "mu" Id "." Exp

  syntax Exp ::= Type
  syntax KResult ::= Type

  configuration <k color="green"> $PGM:Exp </k>
                <tenv color="red"> .Map </tenv>
                <mgu color="blue"> .Mgu </mgu>

  rule I:Int => int
  rule B:Bool => bool
  rule <k> X:Id => T ...</k>  <tenv>... X |-> T:Type ...</tenv>
  rule T1:Type  * T2:Type => T1 = int ~> T2 = int ~> int
  rule T1:Type  / T2:Type => T1 = int ~> T2 = int ~> int
  rule T1:Type  + T2:Type => T1 = int ~> T2 = int ~> int
  rule T1:Type <= T2:Type => T1 = int ~> T2 = int ~> bool
  rule <k> lambda X:Id . E:Exp => Tv -> E ~> tenv(TEnv) ...</k>
       <tenv> TEnv => TEnv[Tv/X] </tenv>
    when fresh(Tv:TypeVar)
  rule T1:Type T2:Type => T1 = (T2 -> Tv) ~> Tv  when fresh(Tv:TypeVar)
  rule if T:Type then T1:Type else T2:Type => T = bool ~> T1 = T2 ~> T1

//  rule let X = E in E' => (lambda X . E') E                         [macro]
  rule <k> let X:Id = T:Type in E:Exp => E ~> tenv(TEnv) ...</k>
       <mgu> Theta:Mgu </mgu>
       <tenv> TEnv
        => TEnv[((forall diff(ftv(applyMgu(Theta, T),.Types),
                              ftv(applyMgu(Theta, types(TEnv)))))
                 applyMgu(Theta, T)) / X]
       </tenv>
  rule <k> X => T[fresh / Tvs]* ...</k>
       <tenv>... X:Id |-> (forall Tvs:Types) T:Type ...</tenv>

  rule letrec F X = E in E' => let F = mu F . lambda X . E in E'        [macro]
  rule <k> mu X:Id . E:Exp => (Tv -> Tv) E ~> tenv(TEnv) ...</k>
          <tenv> TEnv => TEnv[Tv/X] </tenv>
    when fresh(Tv:TypeVar)

  syntax K ::= Type "=" Type
  rule <k> T = T' => . ...</k>  <mgu> Theta:Mgu => updateMgu(Theta,T,T') </mgu>
  rule <k> T:Type => applyMgu(Theta,T) </k>  (<mgu> Theta:Mgu </mgu> => .)

  syntax K ::= tenv(Map)
  rule <k> T:Type ~> (tenv(TEnv) => .) ...</k>  <tenv> _ => TEnv </tenv>
endmodule
