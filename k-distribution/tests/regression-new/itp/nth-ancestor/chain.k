/*
    Coq-style proof of `ancestor_means`
    https://github.com/runtimeverification/casper-proofs/blob/master/Core/AccountableSafety.v
*/

require "proof-script.k"

module CHAIN-SYNTAX

endmodule

module CHAIN

    imports PROOF-SCRIPT
    imports CHAIN-SYNTAX

    /*
        (* abstract representation of a block tree *)
        Variable hash_parent : rel Hash.

        Notation "h1 <~ h2" := (hash_parent h1 h2) (at level 50).

        Definition hash_ancestor h1 h2 :=
         connect hash_parent h1 h2.

        Notation "h1 <~* h2" := (hash_ancestor h1 h2) (at level 50).

        Lemma hash_ancestor_base : forall h1 h2,
          h1 <~ h2 -> h1 <~* h2.
        Proof.
        by apply/connect1.
        Qed.

        Lemma hash_ancestor_step : forall h1 h2 h3,
         h1 <~ h2 -> h2 <~* h3 -> h1 <~* h3.
        Proof.
        move => h1 h2 h3.
        move/connect1.
        by apply/connect_trans.
        Qed.
    */

    syntax Pred ::= Int "<~"  Int
                  | Int "<~*" Int

    rule
    <k> apply("<~*.i") => . ... </k>
    <g> B1 <~ B2 => B1 <~* B2 </g>

    rule
    <k> apply("<~*.i") => . ... </k>
    <g> B1 <~ B2 and B2 <~* B3 => B1 <~* B3 </g>

    /*
        (* predicate stating first hash is ancestor of second hash at the indicated distance *)
        Inductive nth_ancestor : nat -> Hash -> Hash -> Prop :=
        | nth_ancestor_0 : forall h1, nth_ancestor 0 h1 h1
        | nth_ancestor_nth : forall n h1 h2 h3,
            nth_ancestor n h1 h2 -> h2 <~ h3 ->
            nth_ancestor n.+1 h1 h3.
    */

    syntax Pred ::= nth(Int, Int, Int)
                  | block(Int)
                  | Int "==" Int

    rule
    <k> apply("nth.i") => . ... </k>
    <g> block(B) => nth(0, B, B) </g>

    rule
    <k> apply("nth.i") => . ... </k>
    <g> nth(N, B1, B2) and B2 <~ B3
     => nth(N +Int 1, B1, B3) </g>

    rule
    <k> apply("nth.e") => . ... </k>
    <g> nth(0, B1, B2) => B1 == B2 </g>

    rule
    <k> apply("nth.e") => . ... </k>
    <g> nth(N, B1, B3)
     => nth(N -Int 1, B1, ?B2:Int) and ?B2 <~ B3 </g>
        requires N >Int 0

endmodule
