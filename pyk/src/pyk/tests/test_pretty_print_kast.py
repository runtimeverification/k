from typing import Callable, Final, Mapping, Tuple, Union
from unittest import TestCase

from pyk.kast import (
    TRUE,
    KApply,
    KAst,
    KLabel,
    KProduction,
    KRule,
    KSort,
    KTerminal,
    Subst,
)
from pyk.ktool import prettyPrintKast, unparser_for_production

success_production = KProduction(KSort('EndStatusCode'), [KTerminal('EVMC_SUCCESS')], klabel=KLabel('EVMC_SUCCESS_NETWORK_EndStatusCode'))


class PrettyPrintKastTest(TestCase):
    TEST_DATA: Final[Tuple[Tuple[Union[KAst, Subst], str], ...]] = (
        (KRule(TRUE), 'rule  true\n  '),
        (KRule(TRUE, ensures=TRUE), 'rule  true\n  '),
        (KRule(TRUE, ensures=KApply('_andBool_', [TRUE, TRUE])), 'rule  true\n   ensures ( true\n   andBool ( true\n           ))\n  '),
        (Subst({'X': TRUE, 'Y': KApply('_andBool_', [TRUE, TRUE])}), 'X |-> true\nY |-> _andBool_ ( true , true )'),
    )

    SYMBOL_TABLE: Final[Mapping[str, Callable]] = {}

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
