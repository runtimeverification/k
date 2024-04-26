from __future__ import annotations

from typing import TYPE_CHECKING

from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KRewrite, KVariable
from pyk.kast.manip import push_down_rewrites
from pyk.kast.outer import KClaim
from pyk.prelude.ml import mlOr
from pyk.testing import KProveTest

from ..utils import K_FILES

if TYPE_CHECKING:
    from pyk.ktool.kprove import KProve


class TestPrintProveRewrite(KProveTest):
    KOMPILE_MAIN_FILE = K_FILES / 'imp-verification.k'

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
        assert CTerm._is_top(mlOr([res.kast for res in result]))
