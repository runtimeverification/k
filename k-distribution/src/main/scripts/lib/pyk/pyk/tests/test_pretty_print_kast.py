from typing import Callable, Final, Mapping, Tuple
from unittest import TestCase

from pyk.kast import TRUE, KAst, KRule, prettyPrintKast


class PrettyPrintKastTest(TestCase):
    TEST_DATA: Final[Tuple[Tuple[KAst, str], ...]] = (
        (KRule(TRUE), 'rule true'),
        (KRule(TRUE, ensures=TRUE), 'rule true'),
    )

    SYMBOL_TABLE: Final[Mapping[str, Callable]] = {}

    def test(self):
        for i, (kast, expected) in enumerate(self.TEST_DATA):
            with self.subTest(i=i):
                actual = prettyPrintKast(kast, self.SYMBOL_TABLE)
                actual_tokens = actual.split()
                expected_tokens = expected.split()
                self.assertListEqual(actual_tokens, expected_tokens)
