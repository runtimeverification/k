from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kast import KAtt
from pyk.kast.inner import KApply, KLabel, KSort, KVariable
from pyk.kast.outer import KNonTerminal, KProduction, KRule, KTerminal
from pyk.ktool.kprint import pretty_print_kast, unparser_for_production
from pyk.prelude.kbool import TRUE

if TYPE_CHECKING:
    from pyk.kast import KAst


PRETTY_PRINT_TEST_DATA = (
    ('var', KVariable('V'), 'V'),
    ('var-sorted', KVariable('V', sort=KSort('Int')), 'V:Int'),
    ('rule', KRule(TRUE), 'rule  true\n  '),
    ('rule-empty-req', KRule(TRUE, ensures=TRUE), 'rule  true\n  '),
    (
        'rule-req-andbool',
        KRule(TRUE, ensures=KApply('_andBool_', [TRUE, TRUE])),
        'rule  true\n   ensures ( true\n   andBool ( true\n           ))\n  ',
    ),
    ('sort-decl', KProduction(KSort('Test')), 'syntax Test'),
    ('token-decl', KProduction(KSort('Test'), att=KAtt({'token': ''})), 'syntax Test [token()]'),
    (
        'function-decl',
        KProduction(KSort('Test'), [KTerminal('foo'), KNonTerminal(KSort('Int'))], att=KAtt({'function': ''})),
        'syntax Test ::= "foo" Int [function()]',
    ),
    (
        'simple-attributes',
        KAtt({'function': '', 'total': '', 'klabel': 'foo-bar'}),
        '[function(), total(), klabel(foo-bar)]',
    ),
    (
        'location-source-attributes',
        KAtt(
            {
                'org.kframework.attributes.Location': [2135, 3, 2135, 20],
                'org.kframework.attributes.Source': r'/some/path\ with \ spaces/domains.md',
            }
        ),
        r'[org.kframework.attributes.Location(2135,3,2135,20), org.kframework.attributes.Source("/some/path\ with \ spaces/domains.md")]',
    ),
)


@pytest.mark.parametrize(
    'test_id,kast,expected',
    PRETTY_PRINT_TEST_DATA,
    ids=[test_id for test_id, *_ in PRETTY_PRINT_TEST_DATA],
)
def test_pretty_print(test_id: str, kast: KAst, expected: str) -> None:
    # Given
    expected_tokens = expected.split('\n')

    # When
    actual = pretty_print_kast(kast, {})
    actual_tokens = actual.split('\n')

    # Then
    assert actual_tokens == expected_tokens


def test_unparser_underbars() -> None:
    # Given
    success_production = KProduction(
        KSort('EndStatusCode'), [KTerminal('EVMC_SUCCESS')], klabel=KLabel('EVMC_SUCCESS_NETWORK_EndStatusCode')
    )
    unparser = unparser_for_production(success_production)
    expected = 'EVMC_SUCCESS'

    # When
    actual = unparser(KApply('EVMC_SUCCESS_NETWORK_EndStatusCode'))

    # Then
    assert actual == expected
