/*
    Coq-style proof of `ancestor_means`
    https://github.com/runtimeverification/casper-proofs/blob/master/Core/AccountableSafety.v
*/
/*
    Lemma ancestor_means :
      forall n parent new,
      nth_ancestor n parent new -> n > 0 -> parent <~* new.
    Proof.
    elim => //=.
    move => n IH parent new Hn.
    inversion Hn; subst.
    case Hn0: (n == 0).
      move/eqP: Hn0 H0 -> => Hnt Hlt.
      inversion Hnt; subst.
      by apply/connect1.
    move/negP/negP: Hn0 => Hn0 Hltn.
    have Hnn: 0 < n.
      apply: neq0_lt0n.
      by apply/negP/negP.
    move: (IH _ _ H0 Hnn) => Hp.
    apply: connect_trans; eauto.
    by apply/connect1.
*/

require "chain.k"

// inductive case
module NTH2-SPEC
    imports V

    rule
    <g> nth(k(N) +Int 1, B1, B2) => B1 <~* B2 </g>
    <p> .Map => _ </p>
    <k> apply("nth.e")
     ~> store2("p1", "p2")
     ~> load("p1")
     ~> apply("ih")
     ~> load("p2")
     ~> apply("lemma")
     => . </k>
        requires k(N) >Int 0 andBool const(N)

    // induction hypothesis
    rule
    <k> apply("ih") => . ... </k>
    <g> nth(k(N), B1, B2) => B1 <~* B2 </g>
        requires k(N) >Int 0 andBool const(N)
        [trusted]

    /*
        Lemma hash_ancestor_intro' :
          forall h1 h2 h3, h1 <~* h2 -> h2 <~ h3 -> h1 <~* h3.
        Proof.
        move => h1 h2 h3 H1 H2.
        apply: connect_trans; eauto.
        by apply/connect1.
        Qed.
    */
    rule
    <k> apply("lemma") => . ... </k>
    <g> B1 <~* B2 and B2 <~ B3 => B1 <~* B3 </g>
        [trusted]
endmodule

module V
    imports CHAIN

    syntax Bool ::= const(Int) [function, smtlib(con)]

    syntax Int ::= k(Int) [smtlib(k)]

    rule (k(N) +Int 1) -Int 1 => k(N)
endmodule
