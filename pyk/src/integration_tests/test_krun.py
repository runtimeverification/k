from pyk.kast import KApply, KSequence, KToken
from pyk.kastManip import flatten_label, get_cell
from pyk.ktool import KompileBackend
from pyk.prelude.kint import intToken

from .krun_test import KRunTest


class ImpRunTest(KRunTest):
    KOMPILE_MAIN_FILE = 'k-files/imp.k'
    KOMPILE_BACKEND = KompileBackend.HASKELL
    KOMPILE_OUTPUT_DIR = 'definitions/imp'
    KOMPILE_EMIT_JSON = True

    KRUN_USE_DIR = '.imp'

    @staticmethod
    def _update_symbol_table(symbol_table):
        pass

    def test_run(self):
        # Given
        init_pgm_token = KToken('int n , s ; n = 2 ; s = 0 ; while ( 0 <= n ) { s = s + n ; n = n + -1 ; }', 'Pgm')
        final_cterm = self.krun.run(init_pgm_token)

        k_expected = KSequence([])
        state_expected_map_items = [
            KApply('_|->_', [KToken('s', 'Id'), intToken(3)]),
            KApply('_|->_', [KToken('n', 'Id'), intToken(-1)]),
        ]

        k_actual = get_cell(final_cterm.config, 'K_CELL')
        state_actual_map_items = flatten_label('_Map_', get_cell(final_cterm.config, 'STATE_CELL'))

        self.maxDiff = None
        self.assertEqual(k_actual, k_expected)
        self.assertCountEqual(state_actual_map_items, state_expected_map_items)
