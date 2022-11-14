from typing import Optional

from pyk.kast.inner import KApply, KSequence, KToken
from pyk.kast.manip import flatten_label, get_cell
from pyk.kore.parser import KoreParser
from pyk.kore.syntax import DV, App, Pattern, SortApp, String
from pyk.ktool import KompileBackend
from pyk.ktool.kprint import KAstInput, KAstOutput, SymbolTable, _kast
from pyk.prelude.kint import intToken

from .krun_test import KRunTest


class ImpRunTest(KRunTest):
    KOMPILE_MAIN_FILE = 'k-files/imp.k'
    KOMPILE_BACKEND = KompileBackend.HASKELL
    KOMPILE_EMIT_JSON = True

    KRUN_USE_DIR: Optional[str] = '.imp'

    @staticmethod
    def _update_symbol_table(symbol_table: SymbolTable) -> None:
        pass

    def test_run(self) -> None:
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

    def test_run_kore_term(self) -> None:
        # Given
        x = '#token("x", "Id")'
        pattern = self._state(k=f'int {x} ; {x} = 1 ;', state='.Map')
        expected = self._state(k='.', state=f'{x} |-> 1')

        # When
        actual = self.krun.run_kore_term(pattern)

        # Then
        self.assertEqual(actual, expected)

    def _state(self, k: str, state: str) -> Pattern:
        pretty_text = f"""
            <generatedTop>
                <T>
                    <k> {k} </k>
                    <state> {state} </state>
                </T>
                <generatedCounter>
                    0
                </generatedCounter>
            </generatedTop>
        """
        proc_res = _kast(
            definition_dir=self.krun.definition_dir,
            input=KAstInput.RULE,
            output=KAstOutput.KORE,
            expression=pretty_text,
            sort='GeneratedTopCell',
        )
        kore_text = proc_res.stdout
        return KoreParser(kore_text).pattern()


class TmpRunTest(ImpRunTest):
    KRUN_USE_DIR = None


class ConfigTest(KRunTest):
    KOMPILE_MAIN_FILE = 'k-files/config.k'
    KOMPILE_BACKEND = KompileBackend.LLVM

    # TODO Should be unnecessary
    @staticmethod
    def _update_symbol_table(symbol_table: SymbolTable) -> None:
        pass

    def test_run_kore_config(self) -> None:
        # Given
        fst = DV(SortApp('SortInt'), String('0'))
        snd = DV(SortApp('SortInt'), String('1'))
        expected = App(
            "Lbl'-LT-'generatedTop'-GT-'",
            (),
            (
                App(
                    "Lbl'-LT-'T'-GT-'",
                    (),
                    (
                        App("Lbl'-LT-'first'-GT-'", (), (fst,)),
                        App("Lbl'-LT-'second'-GT-'", (), (snd,)),
                    ),
                ),
                App(
                    "Lbl'-LT-'generatedCounter'-GT-'",
                    (),
                    (DV(SortApp('SortInt'), String('0')),),
                ),
            ),
        )

        # When
        actual = self.krun.run_kore_config({'FST': fst, 'SND': snd}, depth=0)

        # Then
        self.assertEqual(actual, expected)
