from typing import Final, Tuple
from unittest import TestCase

from pyk.kast import KApply, KAst, KAtt, KLabel, KNonTerminal, KProduction, KRule, KSort, KTerminal
from pyk.ktool.kprint import SymbolTable, pretty_print_kast, unparser_for_production
from pyk.prelude.kbool import TRUE

success_production = KProduction(
    KSort('EndStatusCode'), [KTerminal('EVMC_SUCCESS')], klabel=KLabel('EVMC_SUCCESS_NETWORK_EndStatusCode')
)


class PrettyPrintKastTest(TestCase):
    TEST_DATA: Final[Tuple[Tuple[KAst, str], ...]] = (
        (KRule(TRUE), 'rule  true\n  '),
        (KRule(TRUE, ensures=TRUE), 'rule  true\n  '),
        (
            KRule(TRUE, ensures=KApply('_andBool_', [TRUE, TRUE])),
            'rule  true\n   ensures ( true\n   andBool ( true\n           ))\n  ',
        ),
        (KProduction(KSort('Test')), 'syntax Test'),
        (KProduction(KSort('Test'), att=KAtt({'token': ''})), 'syntax Test [token()]'),
        (
            KProduction(KSort('Test'), [KTerminal('foo'), KNonTerminal(KSort('Int'))], att=KAtt({'function': ''})),
            'syntax Test ::= "foo" Int [function()]',
        ),
    )

    SYMBOL_TABLE: Final[SymbolTable] = {}

    def test_pretty_print(self) -> None:
        for i, (kast, expected) in enumerate(self.TEST_DATA):
            with self.subTest(i=i):
                actual = pretty_print_kast(kast, self.SYMBOL_TABLE)
                actual_tokens = actual.split('\n')
                expected_tokens = expected.split('\n')
                self.assertListEqual(actual_tokens, expected_tokens)

    def test_unparser_underbars(self) -> None:
        unparser = unparser_for_production(success_production)
        expected = 'EVMC_SUCCESS'
        actual = unparser(KApply('EVMC_SUCCESS_NETWORK_EndStatusCode'))
        self.assertEqual(actual, expected)
