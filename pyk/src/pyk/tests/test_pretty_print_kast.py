from typing import Final, Tuple
from unittest import TestCase

from pyk.kast import KApply, KAst, KLabel, KProduction, KRule, KSort, KTerminal
from pyk.ktool.kprint import (
    SymbolTable,
    prettyPrintKast,
    unparser_for_production,
)
from pyk.prelude import Bool

success_production = KProduction(KSort('EndStatusCode'), [KTerminal('EVMC_SUCCESS')], klabel=KLabel('EVMC_SUCCESS_NETWORK_EndStatusCode'))


class PrettyPrintKastTest(TestCase):
    TEST_DATA: Final[Tuple[Tuple[KAst, str], ...]] = (
        (KRule(Bool.true), 'rule  true\n  '),
        (KRule(Bool.true, ensures=Bool.true), 'rule  true\n  '),
        (KRule(Bool.true, ensures=KApply('_andBool_', [Bool.true, Bool.true])), 'rule  true\n   ensures ( true\n   andBool ( true\n           ))\n  '),
        (KProduction(KSort('Test')), 'syntax Test'),
    )

    SYMBOL_TABLE: Final[SymbolTable] = {}

    def test_pretty_print(self):
        for i, (kast, expected) in enumerate(self.TEST_DATA):
            with self.subTest(i=i):
                actual = prettyPrintKast(kast, self.SYMBOL_TABLE)
                actual_tokens = actual.split('\n')
                expected_tokens = expected.split('\n')
                self.assertListEqual(actual_tokens, expected_tokens)

    def test_unparser_underbars(self):
        unparser = unparser_for_production(success_production)
        expected = 'EVMC_SUCCESS'
        actual = unparser(KApply('EVMC_SUCCESS_NETWORK_EndStatusCode'))
        self.assertEqual(actual, expected)
