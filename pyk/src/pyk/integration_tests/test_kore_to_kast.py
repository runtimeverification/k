from ..kast import KApply
from ..ktool import KompileBackend
from ..prelude import intToken
from .kprove_test import KProveTest


class KoreToKastTest(KProveTest):
    KOMPILE_MAIN_FILE = 'k-files/simple-proofs.k'
    KOMPILE_BACKEND = KompileBackend.HASKELL
    KOMPILE_OUTPUT_DIR = 'definitions/simple-proofs'
    KOMPILE_EMIT_JSON = True

    KPROVE_USE_DIR = '.simple-proof-test'

    @staticmethod
    def _update_symbol_table(symbol_table):
        pass

    def test_kast_to_kore(self):
        kast = KApply('pred1', [intToken(3)])
        kore_expected = None

        kore_actual = self.kprove.kore_to_kast(kast)

        self.assertEqual(kore_actual, kore_expected)
