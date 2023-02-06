from typing import Final

import pytest

from pyk.kast.inner import KApply, KInner, KSort, KToken, KVariable
from pyk.ktool import KProve
from pyk.ktool.kit import parse_token_rule_syntax
from pyk.prelude.kint import intToken

from .utils import KProveTest

TEST_DATA: Final = (
    (
        'variable',
        KToken('N', 'Int'),
        KVariable('N', sort=KSort('K')),
    ),  # TODO: This should parse as an Int, not a K.
    (
        '==Int',
        KToken('N ==Int 1', 'Bool'),
        KApply('_==Int_', KVariable('N', sort=KSort('Int')), intToken(1)),
    ),
)


@pytest.mark.parametrize('test_id,token,expected', TEST_DATA, ids=[test_id for test_id, *_ in TEST_DATA])
class TestParseToken(KProveTest):
    KOMPILE_MAIN_FILE = 'k-files/simple-proofs.k'

    def test_parse_token(self, kprove: KProve, test_id: str, token: KToken, expected: KInner) -> None:
        # When
        actual = parse_token_rule_syntax(kprove, token)

        # Then
        assert actual == expected
