from ..kast import KApply
from ..kore.syntax import DV, App, SortApp, String
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
        __import__('sys').modules['unittest.util']._MAX_LENGTH = 999999999
        kore_kast_pairs = (
            (App('inj', [SortApp('SortBool'), SortApp('SortKItem')], [App('Lblpred1', [], [DV(SortApp('SortInt'), String('3'))])]), KApply('pred1', [intToken(3)])),
        )
        for i, (kore, kast) in enumerate(kore_kast_pairs):
            with self.subTest(i=i):
                kore_actual = self.kprove.kast_to_kore(kast)
                kast_actual = self.kprove.kore_to_kast(kore)
                self.assertEqual(kore_actual, kore)
                self.assertEqual(kast_actual, kast)
