from pyk.kast import KApply
from pyk.kore.syntax import DV, App, SortApp, String
from pyk.ktool import KompileBackend
from pyk.ktool.kprint import SymbolTable
from pyk.prelude.kint import intToken

from .kprove_test import KProveTest


class KoreToKastTest(KProveTest):
    KOMPILE_MAIN_FILE = 'k-files/simple-proofs.k'
    KOMPILE_BACKEND = KompileBackend.HASKELL
    KOMPILE_OUTPUT_DIR = 'definitions/simple-proofs'
    KOMPILE_EMIT_JSON = True

    KPROVE_USE_DIR = '.simple-proof-test'

    @staticmethod
    def _update_symbol_table(symbol_table: SymbolTable) -> None:
        pass

    def test_kast_to_kore(self) -> None:
        kore_kast_pairs = (
            (
                'issue:k/2762',
                App(
                    'inj',
                    [SortApp('SortBool'), SortApp('SortKItem')],
                    [App('Lblpred1', [], [DV(SortApp('SortInt'), String('3'))])],
                ),
                KApply('pred1', [intToken(3)]),
            ),
            # TODO: ('cells-conversion', App("Lbl'-LT-'k'-GT-'", [], [App('EmptyK', [], [])]), KApply('<k>', [EMPTY_K])),
        )
        for (name, kore, kast) in kore_kast_pairs:
            with self.subTest(name):
                kore_actual = self.kprove.kast_to_kore(kast)
                kast_actual = self.kprove.kore_to_kast(kore)
                self.assertEqual(kore_actual, kore)
                self.assertEqual(kast_actual, kast)
