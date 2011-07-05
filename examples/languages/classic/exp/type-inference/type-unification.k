kmod TYPES is including PL-NAT + PL-IF-THEN-ELSE
  sorts BasicType TypeVar Type TypeSchema 
  subsort BasicType TypeVar < Builtins Type 
  subsort Type < TypeSchema 

  ops int bool : -> BasicType 
  op tvar : Nat -> TypeVar 
  op _->_ : Type Type -> Type [prec 10 gather(e E) latex(renameTo _\\ensuremath\\rightarrow_)] 
  op forall_._ : List{TypeVar} Type -> TypeSchema [latex(renameTo \\ensuremath\\forall_._)]

  op _+Type_ : TypeVar Nat -> TypeVar [latex(renameTo _+\\subscript{{\\scriptstyle\\it{}Type}}\_)]
  eq tvar(N) +Type M = tvar(N +Nat M) 

--- free type variables
  op ftv : List{TypeSchema} -> List{TypeVar} 
  eq ftv(BT:BasicType) = .List{TypeVar} 
  eq ftv(Tv:TypeVar) = Tv 
  eq ftv(T1:Type -> T2:Type) = mergeVars(ftv(T1),ftv(T2)) 
  eq ftv(forall Tvl:List`{TypeVar`} . T:Type) = ftv(T) \ Tvl 
  eq ftv(.List{TypeVar}) = .List{TypeVar} 
  eq ftv(Ts1:TypeSchema,Ts2:TypeSchema,Tsl:List`{TypeSchema`}) = mergeVars(ftv(Ts1),ftv(Ts2,Tsl)) 

  op mergeVars : List{TypeVar} List{TypeVar} -> List{TypeVar} 
  eq mergeVars((Tvl1:List`{TypeVar`},Tv,Tvl2:List`{TypeVar`}),(Tvl1':List`{TypeVar`},Tv,Tvl2':List`{TypeVar`})) = mergeVars((Tvl1,Tv,Tvl2),(Tvl1',Tvl2')) 
  eq mergeVars(Tvl,Tvl':List`{TypeVar`}) = Tvl,Tvl' [owise] 

  op _\_ : List{TypeVar} List{TypeVar} -> List{TypeVar} [latex(renameTo _\\ensuremath\\setminus_)]
  eq (Tvl1,Tv,Tvl2) \ (Tvl1',Tv,Tvl2') = (Tvl1,Tvl2) \ (Tvl1',Tvl2') 
  eq Tvl \ Tvl' = Tvl [owise] 

  op |_| : List{TypeVar} -> Nat [latex(renameTo \\ensuremath|_\\ensuremath|)] 
  eq | Tv,Tvl | = 1 +Nat | Tvl | 
  eq | .List{TypeVar} | = 0 

  op _from_ : Nat TypeVar -> List{TypeVar} 
  eq 0 from Tv = .List{TypeVar} 
  eq (sNat N:Nat) from tvar(M:Nat) = tvar(M),(N from tvar(sNat M)) 

--- type substitution: T[Tl / Tvl] substitutes list of type variables Tvl for list of types Tl in T
  op _`[_/_`] : Type List{Type} List{TypeVar} -> Type [prec 2] 
  eq T[.List{TypeVar} / .List{TypeVar}] = T 
  eq T[T1,T2,Tl:List`{Type`} / Tv1:TypeVar,Tv2:TypeVar,Tvl] = T[T1 / Tv1][T2,Tl / Tv2,Tvl] 
  eq BT[T / Tv] = BT 
  eq Tv':TypeVar[T / Tv] = if Tv' ==Bool Tv then T else Tv' fi 
  eq (T1 -> T2)[T / Tv] = T1[T / Tv] -> T2[T / Tv] 

  op typeVar? : Type -> Bool 
  eq typeVar?(tvar(N)) = true 
  eq typeVar?(T) = false [owise]   --- if needed, replace with: eq typeVar?(T1 -> T2) = false .  eq typeVar?(BT) = false 

  op _in_ : TypeVar Type -> Bool 
  eq Tv in BT = false 
  eq Tv in Tv' = Tv ==Bool Tv' 
  eq Tv in (T1 -> T2) = (Tv in T1) orBool (Tv in T2) 

----------------------------------------------------------------------------------------
--- Lists of any type should eventually be builtin; for now, we have to declare them ---
----------------------------------------------------------------------------------------
--- List{TypeVar}
  sort List{TypeVar} 
  subsort TypeVar < List{TypeVar} 
  op .List{TypeVar} : -> List{TypeVar} [latex(renameTo $\\kdot$\\subscript{{\\scriptstyle\\it{}List\\{TypeVar\\}}})]
  op _`,_ : List{TypeVar} List{TypeVar} -> List{TypeVar} [prec 70 assoc id: .List{TypeVar}] 
--- List{Type}
  sort List{Type} 
  subsort Type List{TypeVar} < List{Type} 
  op _`,_ : List{Type} List{Type} -> List{Type} [ditto] 
--- List{TypeSchema}
  sort List{TypeSchema} 
  subsort TypeSchema List{Type} < List{TypeSchema} 
  op _`,_ : List{TypeSchema} List{TypeSchema} -> List{TypeSchema} [ditto] 
endkm



--- equational constraint solving stuff
kmod UNIFICATION is including TYPES + K 

  ops eqn eqns solved started : -> CellLabel 
  op _=_ : Type Type -> SetItem [strat(1 2 0) prec 30] 

  rule [add-constraint] : (<eqn> T:Type = T':Type </eqn> => .Bag) <started_> (.Set => (Solved[T]) = (Solved[T']) )<_/started> 
          <solved> Solved:Set </solved> 
  rule [reflexivity] : <started_> T = T => .Set <_/started> 
  rule [constructors] : <started_> (T1:Type -> T2:Type) = (T1':Type -> T2':Type) => T1 = T1' T2 = T2' <_/started> 
  rule [orient] : <started_> T = Tv:TypeVar => Tv = T <_/started> if notBool typeVar?(T) 
  rule [eqn] : <started> Tv = T Eqns => Eqns[T / Tv] </started> <solved> Solved => Tv = T (Solved[T /right Tv]) </solved>
               if notBool(Tv in T) 

  op _`[_/_`] : Set Type TypeVar -> Set 
  eq .Set[T / Tv] = .Set 
  eq (T1 = T2 Eqns:Set)[T / Tv] = T1[T / Tv] = T2[T / Tv] (Eqns[T / Tv]) 

  op _`[_/right_`] : Set Type TypeVar -> Set 
  eq .Set[T /right Tv] = .Set 
  eq (Tv = T Eqns)[T' /right Tv':TypeVar] = Tv = T[T' / Tv'] (Eqns[T' /right Tv']) 

  op _`[_`] : Set Type -> Type 

  syntax List{Type} ::= Set [[ List{Type} ]] [latex({#1}\llbracket\,{#2}\,\rrbracket)]
---  op _`[`[_`]`] : Set List{Type} -> List{Type} 
--- I would like to use the following operation name instead, but K-Maude does not like it ..
---  op _`[_`] : Set List{Type} -> List{Type} 
  eq .Set[T] = T 
  eq (Tv = T' Eqns)[T] = Eqns[T[T' / Tv]] 
  eq Eqns[[.List{TypeVar}]] = .List{TypeVar} 
  eq Eqns[[T]] = Eqns[T] 
  eq Eqns[[T1,T2,Tl:List`{Type`}]] = Eqns[T1],Eqns[T2],Eqns[[Tl]] 
endkm
