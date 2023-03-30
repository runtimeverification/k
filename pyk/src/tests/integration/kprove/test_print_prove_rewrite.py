from __future__ import annotations

from typing import TYPE_CHECKING

from pyk.kast.inner import KApply, KRewrite, KVariable
from pyk.kast.manip import push_down_rewrites
from pyk.kast.outer import KClaim
from pyk.prelude.ml import is_top

from ..utils import KProveTest

if TYPE_CHECKING:
    pass

    from pyk.ktool.kprove import KProve


class TestPrintProveRewrite(KProveTest):
    KOMPILE_MAIN_FILE = 'k-files/imp-verification.k'

    def test_print_prove_rewrite(self, kprove: KProve) -> None:
        # Given
        claim_rewrite = KRewrite(
            KApply(
                '<T>',
                [
                    KApply('<k>', [KApply('_+_', [KVariable('X'), KVariable('Y')])]),
                    KApply('<state>', [KVariable('STATE')]),
                ],
            ),
            KApply(
                '<T>',
                [
                    KApply('<k>', [KApply('_+Int_', [KVariable('X'), KVariable('Y')])]),
                    KApply('<state>', [KVariable('STATE')]),
                ],
            ),
        )

        expected = '<T>\n  <k>\n    ( X + Y => X +Int Y )\n  </k>\n  <state>\n    STATE\n  </state>\n</T>'

        # When
        minimized_claim_rewrite = push_down_rewrites(claim_rewrite)
        claim = KClaim(minimized_claim_rewrite)
        actual = kprove.pretty_print(minimized_claim_rewrite)
        result = kprove.prove_claim(claim, 'simple-step')

        # Then
        assert actual == expected
        assert is_top(result)
