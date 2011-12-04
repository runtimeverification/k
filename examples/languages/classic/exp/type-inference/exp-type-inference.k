
module EXP-TYPE-INFERENCE-SYNTAX

/*@ \section{Syntax}
Since the EXP type inferencer infers all the types automatically,
without requiring the user to declare any type explicitly, the EXP
syntax needed for the type inferencer is identical to the syntax used
for the dynamic, untyped semantics.  What we need is to change the
strictness of the conditional into strict in all its arguments
(indeed, all three of its arguments need to type), and to make sure
the \texttt{let} binder is not desugared anymore into $\lambda$
(because we want the type inferencer to be let-polymorphic).  Instead,
the \texttt{let} binder is declared to be strict in its second
argument (since the bound expression still needs to be typed). */

//@ \subsection{Arithmetic constructs}

  syntax Exp ::= #Int | #Bool | #Id
               | Exp "+" Exp                    [:strict prec 33 gather(E e):]
               | Exp "-" Exp                    [:strict prec 33 gather(E e):]
               | Exp "*" Exp                    [:strict prec 31 gather(E e):]
               | Exp "/" Exp                    [:strict prec 31 gather(E e):]
               | Exp "%" Exp                    [:strict prec 31 gather(E e):]
               | "-" Exp                        [:strict:]
               | Exp "<" Exp                    [:strict prec 37:]
               | Exp "<=" Exp                   [:strict prec 37:]
               | Exp ">" Exp                    [:strict prec 37:]
               | Exp ">=" Exp                   [:strict prec 37:]
               | Exp "==" Exp                   [:strict prec 37:]
               | Exp "!=" Exp                   [:strict prec 37:]
               | Exp "and" Exp                  [:strict prec 55 gather(E e):]
               | Exp "or" Exp                   [:strict prec 59 gather(E e):]
               | "not" Exp                      [:strict prec 53:]

//@ \subsection{Functional constructs}

  syntax Exp ::= "lambda" #Id "." Exp           [:latex "\lambda{#1}.{#2}":]
               | Exp Exp                        [:strict prec 10 gather(E e):]
               | "if" Exp "then" Exp "else" Exp [:strict:]
               | "mu" #Id "." Exp               [:latex "\mu{#1}.{#2}":]
               | "let" #Id "=" Exp "in" Exp     [:strict(2):]
               | "letrec" #Id #Id "=" Exp in Exp

/*@ \subsection{Desugaring macros}
We only keep the desugaring of \texttt{letrec} into a \texttt{let}.
This way, \texttt{letrec} will also be polymorphic. */

  macro (letrec F:#Id X:#Id = E:Exp in E':Exp)
      = (let F = mu F . (lambda X . E) in E')

end module


module EXP-TYPE-INFERENCE
  imports EXP-TYPE-INFERENCE-SYNTAX

  syntax Exp ::= Type
  syntax KResult ::= Type

  configuration <T color="yellow">
                  <k color="green"> $PGM:Exp </k>
                     <tenv color="LightSkyBlue"> .Map </tenv>
                     <unification>
                       <eqns>
                         <eqn multiplicity="*"> .K </eqn>
                       </eqns>
                       <mgu> .Map </mgu>
                     </unification>
                     <nextType> tv(0) </nextType>
                </T>

  rule <k> I:#Int => int ...</k>
  rule <k> B:#Bool => bool ...</k>
  rule <k> X:#Id => T:Type ...</k> <tenv>... X |-> T ...</tenv>

  rule <k> L:KLabel(T1:Type,,T2:Type) => (T1,T2 = int,int) ~> int ...</k>
    if L ==Bool '_+_ orBool L ==Bool '_-_ orBool
       L ==Bool '_*_ orBool L ==Bool '_/_ orBool L ==Bool '_%_
  rule <k> - T => (T = int) ~> int ...</k>
  rule <k> L(T1,,T2) => (T1,T2 = int,int) ~> bool ...</k>
    if L ==Bool '_<_ orBool L ==Bool '_<=_ orBool L ==Bool '_>_ orBool
       L ==Bool '_>=_ orBool L ==Bool '_==_ orBool L ==Bool '_!=_
  rule <k> L(T1,,T2) => (T1,T2 = bool,bool) ~> bool ...</k>
    if L ==Bool '_and_ orBool L ==Bool '_or_

  rule <k> not T => (T = bool) ~> bool ...</k>
  rule <k> if T then T1 else T2 => (T,T1 = bool,T2) ~> T1 ...</k>

  rule <k> lambda X . E:Exp => E ~> (Tv -> []) ~> tenv(TEnv:Map) ...</k>
          <tenv> TEnv => TEnv[Tv/X] </tenv>
          <nextType> Tv => Tv +Type 1 </nextType>
  rule <k> T1 T2 => (T1 = (T2 -> Tv)) ~> Tv ...</k>
       <nextType> Tv => Tv +Type 1 </nextType>

  rule <k> mu X . E => (E = Tv) ~> tenv(TEnv) ...</k>
          <tenv> TEnv => TEnv[Tv / X] </tenv>
          <nextType> (Tv => Tv +Type 1) </nextType>

  rule <k> let X = T in E => E ~> tenv(TEnv) ...</k>
       <eqns> .Bag </eqns> <mgu> Theta:Map </mgu>
       <tenv> TEnv
        => TEnv[((forall diff(ftv(Theta[T]),ftv(types(TEnv)))) Theta[T])
                   / X]
       </tenv>

  rule <k> X => T[|Tvs| from Tv /* Tvs] ...</k>
       <tenv>... X |-> (forall Tvs) T ...</tenv>
       <nextType> Tv => Tv +Type | Tvs | </nextType>


  rule <k> T => Theta[T] </k> (<eqns> .Bag </eqns> => .) <mgu> Theta </mgu>



// Unification

  rule <k> Ts:Types = Ts':Types => . ...</k>
       (. => <eqn> Theta[Ts]* = Theta[Ts']* </eqn>)
       <mgu> Theta:Map </mgu>

  rule <eqn> Ts = Ts </eqn> => .

  rule <eqn> (T1,T2,Ts) = (T1':Type,T2':Type,Ts') </eqn>
    => <eqn> T1 = T1' </eqn> <eqn> (T2,Ts) = (T2',Ts') </eqn>

  rule <eqn> (T1 -> T2) = (T1' -> T2') </eqn>
    => <eqn> T1 = T1' </eqn> <eqn> T2 = T2' </eqn>

  rule <eqn> (T = Tv) => (Tv = T) </eqn>
    if typeVar(Tv) andBool notBool(typeVar(T))

  rule <eqns> Eqns:Bag <eqn> Tv = T </eqn> => refine(Eqns,Tv,T) </eqns>
       <mgu> Theta => Tv |-> T refine(Theta,Tv,T) </mgu>
    if notBool(Tv inType T)

  syntax Map ::= "refine" "(" Map "," Type "," Type ")"
  rule refine(.Map,_,_) => .Map
  rule refine(Tv'|->T' Theta, Tv, T) => Tv'|->T'[T/Tv] refine(Theta,Tv,T)

  syntax Bag ::= "refine" "(" Bag "," Type "," Type ")"
  rule refine(.Bag,Tv,T) => .Bag
  rule refine(<eqn> T1 = T2 </eqn> Eqns, Tv, T)
    => <eqn> T1[T/Tv] = T2[T/Tv] </eqn> refine(Eqns,Tv,T)


------------------------
--- Auxilliary stuff ---
------------------------

  syntax K ::= "tenv" "(" Map ")"
  rule <k> T ~> (tenv(TEnv) => .) ...</k> <tenv>  _ => TEnv </tenv>
    [:structural:]

// next should probably be generic in some way, for all maps ...
  syntax Types ::= "types" "(" Map ")"
  eq types(X |-> T TEnv) = T,types(TEnv)
  eq types(.Map) = .Types

  syntax Exps ::= List{Exp,","}
  syntax K ::= Type "->" "[]"
             | Exps "=" Exps  [:strict prec(100):]

  rule T ~> (Tv -> []) => Tv -> T




  syntax Type ::= "int" | "bool"        // basic types
                | "tv" #Nat             // type variables
                | Type "->" Type        // function type
  syntax Types ::= List{Type,","}

  syntax #Bool ::= "basicType" "(" Type ")"
                 | "typeVar" "(" Type ")"
  rule basicType(int) => true   [:structural:]
  rule basicType(bool) => true  [:structural:]
  rule typeVar(T) => getKLabel(T) ==Bool 'tv_  [:structural:]

  syntax TypeSchema ::= Type
                      | "(" "forall" Types ")" Type
                          [:latex("(\forall{#1}){#2}"):]
  syntax TypeSchemas ::= List{TypeSchema,","}

  syntax Type ::= Type "+Type" #Nat [:latex("{#1}+_{\it Type}{#2}"):]
  rule tv(N:#Nat) +Type M:#Nat => tv(N +Nat M)  [:structural:]

// Free type variables.  These should be generic and builtin, for all binders.
  syntax Types ::= "ftv" "(" TypeSchemas ")"
  rule ftv(BT:Type) => .Types if basicType(BT)
  rule ftv(Tv:Type) => Tv,.Types if typeVar(Tv)
  rule ftv(T1:Type -> T2:Type) => union(ftv(T1),ftv(T2))
  rule ftv((forall Tvs:Types) T:Type) => diff(ftv(T),Tvs)
  rule ftv(.TypeSchemas) => .Types
  rule ftv(TS1:TypeSchema,TS2:TypeSchema,TSs:TypeSchemas)
    => union(ftv(TS1),ftv(TS2,TSs))

// The operations below should be generic and builtin, for all lists
  syntax Types ::= "union" "(" Types "," Types ")"
                 | "diff" "(" Types "," Types ")"
                 | "insert" "(" Type "," Types ")"
                 | "delete" "(" Type "," Types ")"
  syntax #Nat ::= "|" Types "|"
  rule union(.Types,Ts':Types) => Ts'
  rule union((T,Ts:Types),Ts') => union(Ts,insert(T,Ts'))
  rule diff(Ts,.Types) => Ts
  rule diff(Ts,(T,Ts')) => diff(delete(T,Ts),Ts')
  rule insert(T,.Types) => T,.Types
  rule insert(T,(T',Ts)) => if T ==Bool T' then T',Ts else T',insert(T,Ts) fi
  rule delete(T,.Types) => .Types
  rule delete(T,(T',Ts)) => if T ==Bool T' then Ts else T',delete(T,Ts) fi
  rule |T,Ts| => 1 +Nat |Ts|
  rule |.Types| => 0

// This should be generalized and builtin: fresh name generator
  syntax Types ::= #Nat "from" Type
  rule 0 from tv(_) => .Types
  rule (sNat N:#Nat) from tv(M:#Nat) => tv(M),(N from tv(sNat M))

// This could also be generic: subterm relation?
  syntax #Bool ::= Type "inType" Type [:latex("{#1}\in_{\it Type}{#2}"):]
  rule Tv inType BT  => false if typeVar(Tv) andBool basicType(BT)
  rule Tv inType Tv' => Tv ==Bool Tv' if typeVar(Tv) andBool typeVar(Tv')
  rule Tv inType (T1 -> T2) => (Tv inType T1) orBool (Tv inType T2)

// Type substitution: T[Ts /* Tvs] substitutes list of types Ts for
// list of type variables Tvs.  T[T' / Tv] substitutes type T' for type
// variable Tv in T.  These should also be generic and builtin.
  syntax Type ::= Type "[" Types "/*" Types "]"  [:prec(2):]
                | Type "[" Type  "/"  Type  "]"  [:prec(2):]  // auxilliary
  rule T[.Types /* .Types] => T
  rule T[T1,Ts:Types /* Tv,Tvs] => T[T1 / Tv][Ts /* Tvs]
  rule BT[T / Tv] => BT if basicType(BT) andBool typeVar(Tv)
  rule Tv':Type[T / Tv] => if Tv' ==Bool Tv then T else Tv' fi
    if typeVar(Tv')
  rule (T1 -> T2)[T / Tv] => T1[T / Tv] -> T2[T / Tv]

// Map application.  Should be generic and builtin.
  syntax Types ::= Map "[" Types "]*"  [:prec(1):]
  syntax Type  ::= Map "[" Type  "]"   [:prec(1):]

  rule .[T] => T
  rule (Tv |-> T':Type Theta)[T] => Theta[T[T'/Tv]]

  rule Theta[.Types]* => .Types
  rule Theta[T,Ts:Types]* => Theta[T],Theta[Ts]*

end module
