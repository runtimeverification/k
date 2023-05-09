from __future__ import annotations

from typing import TYPE_CHECKING

from pyk.kast.inner import KAtt, KToken
from pyk.kast.outer import KClaim, KRule
from pyk.prelude.kbool import BOOL
from pyk.prelude.ml import is_top

from ..utils import K_FILES, KProveTest

if TYPE_CHECKING:
    from pyk.ktool.kprove import KProve


class TestSimpleProof(KProveTest):
    KOMPILE_MAIN_FILE = K_FILES / 'simple-proofs.k'

    def test_prove_claim_with_lemmas(self, kprove: KProve) -> None:
        # Given
        claim = KClaim(
            KToken('<k> foo => bar ... </k> <state> 3 |-> 3 </state>', 'TCellFragment'),
            requires=KToken('pred1(4)', BOOL),
        )
        lemma = KRule(
            KToken('pred1(3) => true', BOOL),
            requires=KToken('pred1(4)', BOOL),
            att=KAtt(atts={'simplification': ''}),
        )

        # When
        result1 = kprove.prove_claim(claim, 'claim-without-lemma')
        result2 = kprove.prove_claim(claim, 'claim-with-lemma', lemmas=[lemma])

        # Then
        assert not is_top(result1)
        assert is_top(result2)
