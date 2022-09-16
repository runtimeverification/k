from pyk.kast import KApply, KToken
from pyk.ktool import KompileBackend
from pyk.prelude.kint import intToken

from .kprove_test import KProveTest


class ImpParseTest(KProveTest):
    KOMPILE_MAIN_FILE = 'k-files/imp.k'
    KOMPILE_BACKEND = KompileBackend.HASKELL
    KOMPILE_OUTPUT_DIR = 'definitions/imp'
    KOMPILE_EMIT_JSON = True

    KPROVE_USE_DIR = '.imp'

    @staticmethod
    def _update_symbol_table(symbol_table):
        pass

    def test_parse_token(self):
        test_parses = (
            ('int-token', KToken('3', 'Int'), intToken(3)),
            ('id-token', KToken('abc', 'Id'), KToken('abc', 'Id')),
            ('add-aexp', KToken('3 + 4', 'AExp'), KApply('_+_', [intToken(3), intToken(4)])),
            # TODO: ('add-int', KToken('3 +Int V', 'Int'), KApply('_+Int_', [intToken(3), KVariable('V')])),
            # TODO: ('k-cell', KToken('<k> . </k>', 'KCell'), KApply('<k>', [EMPTY_K])),
        )

        for name, token, kast in test_parses:
            with self.subTest(name):
                actual_kast = self.kprove.parse_token(token)
                self.assertEqual(actual_kast, kast)
