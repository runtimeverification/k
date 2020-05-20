Require Import BinPos.
Require Import ZArith.
Require Import FMapPositive.
Require Import String.

Require Import Setoid.

Set Implicit Arguments.

(** * Maps

  Define maps, by making constructors for
  empty and singleton maps and map union,
  and defining a suitable equivalence relation *)

(* TODO:
   define a well-formedness predicate saying keys are not repeated,
   augment language definition with a proof that all evaluation
   steps preserve it
 *)

Inductive Map (Key Elt : Type) : Type :=
| mapEmpty
| mapItem (k : Key) (v : Elt)
| mapJoin (m1 m2 : Map Key Elt)
.
Arguments mapEmpty [Key Elt].

(** ** Map notations
 *)
Delimit Scope Map with Map.
Bind Scope Map with Map.

Open Scope Map.

Infix "|->" := mapItem (at level 50, no associativity) : Map.
Infix ":*" := mapJoin (at level 60, right associativity) : Map.

(** ** Map equivalence

  Map equivalence is axiomatized by
  identitiy, associativity, commutativity, and congruence of union,
  closed under reflexivity, symmetry, and transitivity.
 *)
Inductive MapEquiv {K E : Type} : Map K E -> Map K E -> Prop :=
| equivUnit : forall m, MapEquiv (m :* mapEmpty) m
| equivComm : forall m1 m2, MapEquiv (m1 :* m2) (m2 :* m1)
| equivAssoc : forall m1 m2 m3, MapEquiv ((m1 :* m2) :* m3) (m1 :* (m2 :* m3))

| equivJoin : forall l1 r1 l2 r2, MapEquiv l1 l2 -> MapEquiv r1 r2 -> MapEquiv (l1 :* r1) (l2 :* r2)
| equivTrans : forall m1 m2 m3, MapEquiv m1 m2 -> MapEquiv m2 m3 -> MapEquiv m1 m3
| equivSym : forall m1 m2, MapEquiv m1 m2 -> MapEquiv m2 m1
| equivRefl : forall m, MapEquiv m m
.

Infix "~=" := MapEquiv (at level 70, no associativity) : Map.

(** Registering map equivalence as an equivalence relation *)

Add Parametric Relation (K E : Type) : (Map K E) MapEquiv
  reflexivity proved by equivRefl                        
  symmetry proved by equivSym
  transitivity proved by equivTrans
  as map_equiv_rel.

Add Parametric Morphism K E : (@mapJoin K E) with
  signature MapEquiv ==> MapEquiv ==> MapEquiv as map_join_mor.
Proof. auto using equivJoin. Qed.

(** Some derived equivalences *)

(** A unit law with the unit on the left *)
Lemma equivUnitL : forall {K V} (m : Map K V), MapEquiv (mapEmpty :* m) m.
intros. rewrite equivComm. apply equivUnit.
Qed.

(** Switching the first two maps in a right-associated sequence *)
Lemma equivComAssoc : forall {K V} (m1 m2 m3 : Map K V), m1 :* m2 :* m3 ~= m2 :* m1 :* m3.
intros. rewrite <- equivAssoc, (equivComm m1 m2), equivAssoc. reflexivity. Qed.

(** ** Map Equality Tactic

  The map equality tactic [equate_maps] tries to solve map equations involving
  at most one map-typed evar.

  The general approach is to put both maps into a standard form,
  as a sequence of singleton items and residual map-typed variables,
  then cancel entries between the sides, until everything that's
  left can be absorbed into the evar (or we're stuck with
  a residual equation).
 *)

(** *** Finding items in a map
    These are the tactics for commuting target items to the
    head of a map *)

(** Specializing congruence for the find tactic *)
Definition equivJoinL {K V} (r : Map K V) l1 l2 pfl : l1 :* r ~= l2 :* r :=
  equivJoin pfl (equivRefl r).
Definition equivJoinR {K V} (l : Map K V) r1 r2 pfr :  l :* r1 ~= l :* r2 :=
  equivJoin (equivRefl l) pfr.

(** Find an entry with key [x] in map [map].
    If found, it calls the continuation tactic [k] on
    an equality of the form [map ~= x |-> _ :* _],
    otherwise it simply fails.
 *)
Ltac find x map k :=
  match map with
    | (x |-> _) => let pf := constr:(equivSym (equivUnit map)) in k pf
    | (x |-> _ :* _) => let pf := constr:(equivRefl map) in k pf
    | (?mapl :* (x |-> ?v)) => let pf := constr:(equivComm mapl (x |-> v)) in k pf
    | ?mapl :* ?mapr =>
           find x mapl ltac:(fun pfl => let pf := constr:(equivTrans (equivJoinL mapr pfl)
                                                                   (equivAssoc (x |-> _) _ mapr))
                                        in k pf)
        || find x mapr ltac:(fun pfr => let pf := constr:(equivTrans (equivJoinR mapl pfr)
                                                                   (equivComAssoc mapl (x |-> _) _))
                                        in k pf)
  end.

(** Find an entire map [submap] appearing exactly all or part of a map [map].
    It's expeted that [submap] be a variable, this tactic makes no attempt
    to search search up to map equality if [submap] is a more complicated
    map expression.
    If found, calls the continuation tactic [k] on an equality of the form
    [map ~= submap :* _]
 *)
Ltac find_submap map submap k :=
  match map with
    | submap => let pf := constr:(equivSym (equivUnit map)) in k pf
    | (submap :* _) => let pf := constr:(equivRefl map) in k pf
    | (?mapl :* submap) => let pf := constr:(equivComm mapl submap) in k pf
    | ?mapl :* ?mapr =>
           find_submap mapl submap

                       ltac:(fun pfl => let pf := constr:(equivTrans (equivJoinL mapr pfl)
                                                                   (equivAssoc submap _ mapr))
                                        in k pf)
        || find_submap mapr submap
                       ltac:(fun pfr => let pf := constr:(equivTrans (equivJoinR mapl pfr)
                                                                   (equivComAssoc mapl submap _))
                                        in k pf)
  end.

(** *** Map well-formedness predicates

    [check_maps] checks that each map is right associated,
    has items before map-typed ordinary variables before
    evars, and that there is at most one evar, on the right side.

    [is_map_exp] is also used elsewhere, and succeeds only if the given
    map is neither an evar nor any of the map constructors.
 *)

Ltac is_map_exp m :=
  match m with
    | (_ |-> _) => fail 1
    | (_ :* _) => fail 1
    | mapEmpty => fail 1
    | _ => try (is_evar m;fail 2)
  end.
Ltac check_left_var_map m :=
  match m with
    | (?l :* ?m') => is_map_exp l;check_left_var_map m'
    | _ => is_map_exp m
  end.
Ltac check_left_map m :=
  match m with
    | mapEmpty => idtac
    | _ |-> _ => idtac
    | (_ |-> _ :* ?m') => check_left_map m'
    | _ => check_left_var_map m
  end.
Ltac check_right_var_map m :=
  match m with
    | (?l :* ?m') => is_map_exp l;check_right_var_map m'
    | _ => first [is_evar m | is_map_exp m]
  end.
Ltac check_right_map m :=
  match m with
    | mapEmpty => idtac
    | _ |-> _ => idtac
    | (_ |-> _ :* ?m') => check_right_map m'
    | _ => check_right_var_map m
  end.
Ltac check_maps :=
  match goal with
    | [|- ?l ~= ?r] => check_left_map l;check_right_map r
  end.

(** *** Preparing maps.

    An equation is prepared by using any map equation hypotheses to
    expand variables in the maps involed,
    then using map equalities to remove empties, right-associate
    unions, and move singleton items to the front.

    This tactic isn't entirely careful about locating evars,
    but they are checked afterwards.
 *)
Ltac expand_map m :=
  match m with
    | ?l :* ?r => expand_map l; expand_map r
    | ?v => is_var v;
           match goal with
             | [H : v ~= ?m |- _] => rewrite !H;clear H;expand_map m
             | [H : ?m ~= v |- _] => rewrite <- !H;clear H;expand_map m
           end
    | _ => idtac
  end.


(* maybe do by reflection? *)
Ltac prepare_maps :=
  match goal with
    | [|- ?l ~= ?r] => expand_map l;expand_map r
  end;
  repeat
    match goal with
        | [|- context [mapEmpty :* ?m]] => rewrite (equivUnitL m)
        | [|- context [?m :* mapEmpty]] => rewrite (equivUnit m)
        | [|- context [(?m1 :* ?m2) :* ?m3]] => rewrite (equivAssoc m1 m2 m3)
  end;
  (* switch if left side has a map evar *)
  match goal with
    | [|- ?l ~= ?r] =>
        match l with
          | context [?v] => is_evar v;
            match type of v with Map _ _  => symmetry end
        end
    | _ => idtac
  end;
  (* Now commute items to the front things *)
  repeat match goal with
           | [|- context [?m1 :* ?m2 :* ?m3]] =>
             match m2 with _ |-> _ => is_map_exp m1; rewrite (equivComAssoc m1 m2 m3)
             end
           | [|- context [?m1 :* ?m2]] =>
             match m2 with _ |-> _ => is_map_exp m1; rewrite (equivComm m1 m2)
             end
         end
  .

(* *** Solving the map equation

   After preparing the maps, the left side has no evars, so the non-evar
   part of the RHS must appear as a submap of the left side.

   This tactic proceeds item by item, finding and cancelling identical
   items between sides.
   If this ends with an equation between a map and an evar it is
   instantiated.

   If the equation isn't completely solved, the tactic still succeeds,
   leaving the reduced equation.
 *)
Ltac equate_maps :=
  prepare_maps;
  first[check_maps| fail 1];
  (* Find item or submap when rhs has a join *)
  repeat match goal with
  | [|- MapEquiv ?map (?x |-> _ :* _)] => find x map
      ltac:(fun pf => apply (equivTrans pf);apply equivJoinR)
  | [|- MapEquiv ?map (?submap :* _)] => find_submap map submap
      ltac:(fun pf => apply (equivTrans pf);apply equivJoinR)
  end;
  (* If we're not failing, the rhs is down to a join-free map.
     Because the lhs is still in prepared form, reflexivity
     can handle all the remaining solvable possibilities.
    *)
  try reflexivity.