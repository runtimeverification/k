from typing import Iterable, Tuple

from pyk.kast import KApply, KInner, KSort, KToken, KVariable
from pyk.ktool import KompileBackend
from pyk.ktool.kit import parse_token_rule_syntax
from pyk.ktool.kprint import SymbolTable
from pyk.prelude.kint import intToken

from .kprove_test import KProveTest


class ParseTokenTest(KProveTest):
    KOMPILE_MAIN_FILE = 'k-files/simple-proofs.k'
    KOMPILE_BACKEND = KompileBackend.HASKELL
    KOMPILE_OUTPUT_DIR = 'definitions/simple-proofs'
    KOMPILE_EMIT_JSON = True

    KPROVE_USE_DIR = '.simple-proof-test'

    @staticmethod
    def _update_symbol_table(symbol_table: SymbolTable) -> None:
        pass

    def test_parse_token(self) -> None:
        tests: Iterable[Tuple[str, KToken, KInner]] = (
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

        for (name, token, expected) in tests:
            with self.subTest(name):
                actual = parse_token_rule_syntax(self.kprove, token)
                self.assertEqual(actual, expected)
