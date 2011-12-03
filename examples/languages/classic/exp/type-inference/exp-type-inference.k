
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
                     <nextType> tvar(0) </nextType>
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
          <nextType> Tv:TypeVar => Tv +Type 1 </nextType>
  rule <k> T1 T2 => (T1 = (T2 -> Tv)) ~> Tv ...</k>
       <nextType> Tv => Tv +Type 1 </nextType>

  rule <k> mu X . E => (E = Tv) ~> tenv(TEnv) ...</k>
          <tenv> TEnv => TEnv[Tv / X] </tenv>
          <nextType> (Tv => Tv +Type 1) </nextType>

  rule <k> let X = T in E => E ~> tenv(TEnv) ...</k>
       <eqns> .Bag </eqns> <mgu> Theta:Map </mgu>
       <tenv> TEnv
        => TEnv[((forall (ftv(Theta[T]) \ ftv(Theta[types(TEnv)]))) Theta[T])
                   / X]
       </tenv>

  rule <k> X => T[|Tvs| from Tv / Tvs] ...</k>
       <tenv>... X |-> (forall Tvs) T ...</tenv>
       <nextType> Tv => Tv +Type | Tvs | </nextType>



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




  syntax BasicType ::= "int"
                     | "bool"
  syntax TypeVar ::= "tvar" "(" #Nat ")"
                   | TypeVar "+Type" #Nat [:latex("{#1}+_{\it Type}{#2}"):]
  syntax TypeVars ::= List{TypeVar,","}
  syntax Type ::= BasicType | TypeVar
                | Type "->" Type
  syntax Types ::= List{Type,","}
  syntax TypeSchema ::= Type
                      | "(" "forall" TypeVars ")" Type
                          [:latex("(\forall{#1}){#2}"):]
  syntax TypeSchemas ::= List{TypeSchema,","}

  rule tvar(N:#Nat) +Type M:#Nat = tvar(N +Nat M)  [:structural:]

--- free type variables

  syntax TypeVars ::= "ftv" "(" TypeSchemas ")"
  rule ftv(BT:BasicType) => .TypeVars
  rule ftv(Tv:TypeVar) => Tv
  rule ftv(T1:Type -> T2:Type) => mergeVars(ftv(T1),ftv(T2))
  rule ftv((forall Tvs:TypeVars) T:Type) => ftv(T) \ Tvs
  rule ftv(.TypeSchemas) => .TypeVars
  rule ftv(TS1:TypeSchema,TS2:TypeSchema,TSs:TypeSchemas)
    => mergeVars(ftv(TS1),ftv(TS2,TSs))

  syntax TypeVars ::= "mergeVars" "(" TypeVars "," TypeVars ")"
  rule mergeVars(.TypeVars,Tvs':TypeVars) => Tvs'
  rule mergeVars((Tv1,Tv2,Tvs => Tv2,Tvs),(Tvs' => mergeVars(Tv1,Tvs')))
  rule mergeVars(Tv1:TypeVar,(Tv2:TypeVar,Tvs:TypeVars))
    => if Tv1 ==Bool Tv2 then Tv2,Tvs else Tv2,mergeVars(Tv1,Tvs) fi

  syntax TypeVars ::= TypeVars \ TypeVars  [:latex("{#1}\setminus{#2}"):]
  rule (Tv1,Tv2,Tvs) \ Tvs' => mergeVars((Tv1 \ Tvs'),((Tv2,Tvs) \ Tvs'))
  rule .TypeVars \ _ => .TypeVars
  rule Tv1 \ (Tv2,Tvs2:TypeVars)
    => if Tv1 ==Bool Tv2 then .TypeVars else Tv1 \ Tvs2 fi
  rule Tv1 \ .TypeVars => Tv1,.TypeVars

  syntax #Nat ::= "|" TypeVars "|"
  rule |Tv,Tvs| => 1 +Nat |Tvs| 
  rule |.TypeVars| => 0 

  syntax TypeVars ::= #Nat "from" TypeVar
  rule 0 from Tv => .TypeVars
  rule (sNat N:#Nat) from tvar(M:#Nat) => tvar(M),(N from tvar(sNat M))

--- type substitution: T[Ts / Tvs] substitutes list of
--- type variables Tvs for list of types Ts in T

  syntax Type ::= Type "[" Types "/" TypeVars "]"  [:prec(2):]

  rule T[.Types / .TypeVars] => T
  rule T[T1,T2,Ts:Types / Tv1,Tv2,Tvs] => T[T1 / Tv1][T2,Ts / Tv2,Tvs]
  rule BT[T / Tv] => BT
  rule Tv':TypeVar[T / Tv] => if Tv' ==Bool Tv then T else Tv' fi
  rule (T1 -> T2)[T / Tv] => (T1[T / Tv]) -> (T2[T / Tv])



  syntax #Bool ::= TypeVar "in" Type
  rule Tv in BT => false 
  rule Tv in Tv' => Tv ==Bool Tv' 
  rule Tv in (T1 -> T2) => (Tv in T1) orBool (Tv in T2)


  syntax Exps ::= List{Exp,","}
  syntax K ::= TypeVar "->" "[]"
             | Exps = Exps  [:strict prec(100):]

  rule T ~> (Tv -> []) => Tv -> T

  rule <k> Ts:Types = Ts':Types => . ...</k>
       (. => <eqn> Theta[Ts] = Theta[Ts'] </eqn>)
       <mgu> Theta </mgu>

***(
  rule <eqn> Ts = Ts </eqn> => .

  rule <eqn> (T1,T2,Ts) = (T1':Type,T2':Type,Ts') </eqn>
       <eqn> T1 = T1' </eqn> <eqn> (T2,Ts) = (T2',Ts') </eqn>

  rule <eqn> (T1 -> T2) = (T1' -> T2') </eqn>
    => <eqn> T1 = T1' </eqn> <eqn> T2 = T2' </eqn>

  rule (<eqn> Tv = T </eqn> => .)
       <mgu>... . => Tv |-> T ...</mgu>
    if notBool (Tv in T)
***)

  syntax Types ::= Map "[" Types "]"

  rule .Map[T] => T
  rule (Tv |-> T':Type Theta)[T] => Theta[T[T' / Tv]] 

---  rule Theta[.Types] => .Types
---  rule Theta[T1,T2,Ts:Types] => Theta[T1],Theta[T2,Ts]

end module
