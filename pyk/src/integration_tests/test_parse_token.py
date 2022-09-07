from typing import Iterable, Tuple

from pyk.kast import KApply, KAtt, KInner, KToken, KVariable
from pyk.ktool import KompileBackend
from pyk.ktool.kit import parse_token_rule_syntax
from pyk.prelude import intToken
from pyk.utils import FrozenDict

from .kprove_test import KProveTest


class ParseTokenTest(KProveTest):
    KOMPILE_MAIN_FILE = 'k-files/simple-proofs.k'
    KOMPILE_BACKEND = KompileBackend.HASKELL
    KOMPILE_OUTPUT_DIR = 'definitions/simple-proofs'
    KOMPILE_EMIT_JSON = True

    KPROVE_USE_DIR = '.simple-proof-test'

    @staticmethod
    def _update_symbol_table(symbol_table):
        pass

    def test_parse_token(self) -> None:
        def vattr(sort: str) -> KAtt:
            return KAtt(FrozenDict({'org.kframework.kore.Sort': FrozenDict({'node': 'KSort', 'name': sort})}))

        tests: Iterable[Tuple[str, KToken, KInner]] = (
            ('variable', KToken('N', 'Int'), KVariable('N', vattr('K'))),  # TODO: This should parse as an int.
            (
                '==Int',
                KToken('N ==Int 1', 'Bool'),
                KApply('_==Int_', KVariable('N', vattr('Int')), intToken(1)),
            ),
        )

        for (name, token, expected) in tests:
            with self.subTest(name):
                actual = parse_token_rule_syntax(self.kprove, token)
                self.assertEqual(actual, expected)
