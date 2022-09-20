from pyk.kast import KApply, KSequence, KToken, KVariable
from pyk.kastManip import remove_attrs
from pyk.ktool import KompileBackend
from pyk.ktool.kprint import SymbolTable
from pyk.prelude.kint import intToken

from .kprove_test import KProveTest


class ImpParseTest(KProveTest):
    KOMPILE_MAIN_FILE = 'k-files/imp.k'
    KOMPILE_BACKEND = KompileBackend.HASKELL
    KOMPILE_OUTPUT_DIR = 'definitions/imp'
    KOMPILE_EMIT_JSON = True

    KPROVE_USE_DIR = '.imp'

    @staticmethod
    def _update_symbol_table(symbol_table: SymbolTable) -> None:
        pass

    def test_parse_token(self) -> None:
        test_parses = (
            ('int-token', False, KToken('3', 'Int'), intToken(3)),
            ('id-token', False, KToken('abc', 'Id'), KToken('abc', 'Id')),
            ('add-aexp', False, KToken('3 + 4', 'AExp'), KApply('_+_', [intToken(3), intToken(4)])),
            ('add-int', True, KToken('3 +Int V', 'Int'), KApply('_+Int_', [intToken(3), KVariable('V')])),
            ('k-cell', True, KToken('<k> . </k>', 'KCell'), KApply('<k>', KSequence())),
        )

        for name, as_rule, token, kast in test_parses:
            with self.subTest(name):
                actual_kast = self.kprove.parse_token(token, as_rule=as_rule)
                self.assertEqual(remove_attrs(actual_kast), kast)
