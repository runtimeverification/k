from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kast.inner import KApply, KSequence, KToken, KVariable
from pyk.kast.manip import remove_attrs
from pyk.prelude.kint import INT, intToken

from .utils import KPrintTest

if TYPE_CHECKING:
    from typing import Final

    from pyk.kast import KInner
    from pyk.ktool.kprint import KPrint


TEST_DATA: Final = (
    ('int-token', False, KToken('3', 'Int'), intToken(3)),
    ('id-token', False, KToken('abc', 'Id'), KToken('abc', 'Id')),
    ('add-aexp', False, KToken('3 + 4', 'AExp'), KApply('_+_', [intToken(3), intToken(4)])),
    ('add-int', True, KToken('3 +Int V', 'Int'), KApply('_+Int_', [intToken(3), KVariable('V', sort=INT)])),
    ('k-cell', True, KToken('<k> . </k>', 'KCell'), KApply('<k>', KSequence())),
    (
        'imp-config',
        True,
        KToken(
            """
            <generatedTop>
                <T>
                    <k> int #token("x", "Id") ; #token("x", "Id") = 0 ; </k>
                    <state> .Map </state>
                </T>
                <generatedCounter>
                    0
                </generatedCounter>
            </generatedTop>
            """,
            'GeneratedTopCell',
        ),
        KApply(
            '<generatedTop>',
            KApply(
                '<T>',
                KApply(
                    '<k>',
                    KApply(
                        'int_;_',
                        KApply('_,_', KToken('x', 'Id'), KApply('.List{"_,_"}_Ids')),
                        KApply('_=_;', KToken('x', 'Id'), KToken('0', 'Int')),
                    ),
                ),
                KApply('<state>', KApply('.Map')),
            ),
            KApply('<generatedCounter>', KToken('0', 'Int')),
        ),
    ),
)


class TestParseToken(KPrintTest):
    KOMPILE_MAIN_FILE = 'k-files/imp.k'

    @pytest.mark.parametrize('test_id,as_rule,token,expected', TEST_DATA, ids=[test_id for test_id, *_ in TEST_DATA])
    def test_parse_token(
        self,
        kprint: KPrint,
        test_id: str,
        as_rule: bool,
        token: KToken,
        expected: KInner,
    ) -> None:
        # When
        actual = kprint.parse_token(token, as_rule=as_rule)

        # Then
        assert remove_attrs(actual) == expected

    # Test that printing a definition is possible without error.
    def test_print_definition(self, kprint: KPrint) -> None:
        kprint.pretty_print(kprint.definition)
