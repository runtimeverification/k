Set Implicit Arguments.

Section relations.
Variables (cfg : Set) (cstep : cfg -> cfg -> Prop).

Definition Spec : Type := cfg -> (cfg -> Prop) -> Prop.

(* Soundness *)
CoInductive reaches (k : cfg) (P : cfg -> Prop) : Prop :=
  | rdone : P k -> reaches k P
  | rstep : forall k', cstep k k' -> reaches k' P -> reaches k P.

Definition sound (Rules : Spec) : Prop :=
  forall x P, Rules x P -> reaches x P.

Inductive step (X : Spec) (k : cfg) (P : cfg -> Prop) : Prop :=
  | sdone : P k -> step X k P
  | sstep : forall k', cstep k k' -> X k' P -> step X k P
  .

CoFixpoint stable_sound (Rules : Spec)
  (Hstable : forall x P, Rules x P -> step Rules x P)
  : sound Rules :=
  fun x P H =>
  match Hstable _ _ H with
    | sdone pf => rdone _ _ pf
    | sstep k' Hstep H' =>
        rstep Hstep (stable_sound Hstable _ _ H')
  end.

Inductive trans (X : Spec) (k : cfg) (P : cfg -> Prop) : Prop :=
  | ddone : P k -> trans X k P
  | dtrans : forall Q, X k Q -> (forall k', Q k' -> trans X k' P) -> trans X k P
  | dstep : forall k', cstep k k' -> trans X k' P -> trans X k P
  .

Lemma trans_trans (X : Spec) :
  forall x P Q,
    trans X x P -> (forall y, P y -> trans X y Q) -> trans X x Q.
induction 1;eauto using trans.
Qed.

Lemma trans_stable (Rules : Spec) :
  (forall x P, Rules x P -> step (trans Rules) x P)
  -> forall x P, trans Rules x P -> step (trans Rules) x P.
induction 2;try econstructor(eassumption).
destruct (H _ _ H0);eauto using step,trans_trans.
Qed.

Lemma proved_sound (Rules : Spec) :
  (forall x P, Rules x P -> step (trans Rules) x P)
  -> sound Rules.
unfold sound.
intros.
apply stable_sound with (trans Rules);
eauto using trans, trans_stable.
Qed.

End relations.
