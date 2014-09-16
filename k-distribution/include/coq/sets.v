Require Import BinPos.
Require Import ZArith.
Require Import FMapPositive.
Require Import String.

Require Import Setoid.

Require Import maps.

Set Implicit Arguments.

(* Sets, similarly to Map *)

Inductive MultiSet (Elt : Type) :=
| setEmpty
| setItem (e : Elt)
| setJoin (s1 s2 : MultiSet Elt)
.
Arguments setEmpty [Elt].

Inductive SetEquiv {E : Type} : MultiSet E -> MultiSet E -> Prop :=
| equivUnit : forall s, SetEquiv (setJoin s setEmpty) s
| equivComm : forall s1 s2, SetEquiv (setJoin s1 s2) (setJoin s2 s1)
| equivAssoc : forall s1 s2 s3, SetEquiv (setJoin (setJoin s1 s2) s3) (setJoin s1 (setJoin s2 s3))

| equivJoin : forall l1 r1 l2 r2, SetEquiv l1 l2 -> SetEquiv r1 r2
    -> SetEquiv (setJoin l1 r1) (setJoin l2 r2)
| equivTrans : forall s1 s2 s3, SetEquiv s1 s2 -> SetEquiv s2 s3 -> SetEquiv s1 s3
| equivSym : forall s1 s2, SetEquiv s1 s2 -> SetEquiv s2 s1
| equivRefl : forall s, SetEquiv s s
.

Lemma equivCommAssoc : forall {E} (s1 s2 s3 : MultiSet E),
  SetEquiv (setJoin s1 (setJoin s2 s3))
           (setJoin s2 (setJoin s1 s3)).
intros.
eapply equivTrans.
apply equivSym. apply equivAssoc.
eapply equivTrans.
eapply equivJoin.
eapply equivComm.
eapply equivRefl.
eapply equivAssoc.
Qed.

Add Parametric Relation (E : Type) : (MultiSet E) SetEquiv
  reflexivity proved by equivRefl                        
  symmetry proved by equivSym
  transitivity proved by equivTrans
  as map_equiv_rel.

Add Parametric Morphism (E : Type) : (@setJoin E) with
  signature SetEquiv ==> SetEquiv ==> SetEquiv as set_join_mor.
Proof. auto using equivJoin. Qed.
Add Parametric Morphism E : (@SetEquiv E) with
  signature SetEquiv ==> SetEquiv ==> iff as set_equiv_mor.
Proof. split;eauto using equivTrans,equivSym. Qed.

Fixpoint keys {Key Elt} (m : Map Key Elt) : MultiSet Key :=
match m with
| mapEmpty => @setEmpty Key
| mapItem k _ => setItem k
| mapJoin l r => setJoin (keys l) (keys r)
end.

Add Parametric Morphism K E : (@keys K E) with
  signature MapEquiv ==> SetEquiv as keys_mor.
induction 1; try solve[econstructor(eassumption)].
Qed.

Lemma equivs {Key Elt} (m1 m2 : Map Key Elt) :
  m1 ~= m2 -> SetEquiv (keys m1) (keys m2).
induction 1;solve[econstructor(eassumption)].
Qed.