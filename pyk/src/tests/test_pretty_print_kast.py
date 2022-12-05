import pytest

from pyk.kast.inner import KApply, KAst, KAtt, KLabel, KSort, KVariable
from pyk.kast.outer import KNonTerminal, KProduction, KRule, KTerminal
from pyk.ktool.kprint import pretty_print_kast, unparser_for_production
from pyk.prelude.bytes import bytesToken
from pyk.prelude.kbool import TRUE

PRETTY_PRINT_TEST_DATA = (
    ('var', KVariable('V'), 'V'),
    ('var-sorted', KVariable('V', sort=KSort('Int')), 'V:Int'),
    (
        'bytes-token',
        bytesToken(''.join(map(chr, range(0, 256)))),
        'b"\\x00\\x01\\x02\\x03\\x04\\x05\\x06\\x07\\x08\\t\\n\\x0b\\f\\r\\x0e\\x0f\\x10\\x11\\x12\\x13\\x14\\x15\\x16\\x17\\x18\\x19\\x1a\\x1b\\x1c\\x1d\\x1e\\x1f !\\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\\\]^_`abcdefghijklmnopqrstuvwxyz{|}~\\x7f\\x80\\x81\\x82\\x83\\x84\\x85\\x86\\x87\\x88\\x89\\x8a\\x8b\\x8c\\x8d\\x8e\\x8f\\x90\\x91\\x92\\x93\\x94\\x95\\x96\\x97\\x98\\x99\\x9a\\x9b\\x9c\\x9d\\x9e\\x9f\\xa0\\xa1\\xa2\\xa3\\xa4\\xa5\\xa6\\xa7\\xa8\\xa9\\xaa\\xab\\xac\\xad\\xae\\xaf\\xb0\\xb1\\xb2\\xb3\\xb4\\xb5\\xb6\\xb7\\xb8\\xb9\\xba\\xbb\\xbc\\xbd\\xbe\\xbf\\xc0\\xc1\\xc2\\xc3\\xc4\\xc5\\xc6\\xc7\\xc8\\xc9\\xca\\xcb\\xcc\\xcd\\xce\\xcf\\xd0\\xd1\\xd2\\xd3\\xd4\\xd5\\xd6\\xd7\\xd8\\xd9\\xda\\xdb\\xdc\\xdd\\xde\\xdf\\xe0\\xe1\\xe2\\xe3\\xe4\\xe5\\xe6\\xe7\\xe8\\xe9\\xea\\xeb\\xec\\xed\\xee\\xef\\xf0\\xf1\\xf2\\xf3\\xf4\\xf5\\xf6\\xf7\\xf8\\xf9\\xfa\\xfb\\xfc\\xfd\\xfe\\xff"',
    ),
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
