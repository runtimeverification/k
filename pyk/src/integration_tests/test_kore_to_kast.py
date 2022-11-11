from pyk.kast import KApply, KLabel, KSequence, KSort, KVariable
from pyk.kore.syntax import DV, And, App, Ceil, Equals, EVar, SortApp, String
from pyk.ktool import KompileBackend
from pyk.ktool.kprint import SymbolTable
from pyk.prelude.kbool import TRUE
from pyk.prelude.kint import intToken

from .kprove_test import KProveTest


class KoreToKastTest(KProveTest):
    KOMPILE_MAIN_FILE = 'k-files/simple-proofs.k'
    KOMPILE_BACKEND = KompileBackend.HASKELL
    KOMPILE_EMIT_JSON = True

    @staticmethod
    def _update_symbol_table(symbol_table: SymbolTable) -> None:
        pass

    def test_bidirectional(self) -> None:
        kore_kast_pairs = (
            (
                'domain-value',
                KSort('Int'),
                DV(SortApp('SortInt'), String('3')),
                intToken(3),
            ),
            (
                'variable-with-sort',
                KSort('Int'),
                EVar('VarX', SortApp('SortInt')),
                KVariable('X', sort=KSort('Int')),
            ),
            (
                'variable-with-super-sort',
                KSort('Bar'),
                App('inj', [SortApp('SortBaz'), SortApp('SortBar')], [EVar('VarX', SortApp('SortBaz'))]),
                KVariable('X', sort=KSort('Baz')),
            ),
            (
                'variable-with-underscore',
                KSort('Int'),
                EVar("VarX'Unds'Y", SortApp('SortInt')),
                KVariable('X_Y', sort=KSort('Int')),
            ),
            (
                'issue:k/2762',
                KSort('Bool'),
                App('Lblpred1', [], [DV(SortApp('SortInt'), String('3'))]),
                KApply('pred1', [intToken(3)]),
            ),
            (
                'cells-conversion',
                KSort('KCell'),
                App("Lbl'-LT-'k'-GT-'", [], [App('dotk', [], [])]),
                KApply('<k>', [KSequence()]),
            ),
            (
                'constrained-term',
                KSort('KCell'),
                And(
                    SortApp('SortKCell'),
                    App("Lbl'-LT-'k'-GT-'", [], [App('dotk', [], [])]),
                    EVar('VarX', SortApp('SortKCell')),
                ),
                KApply(
                    KLabel('#And', params=[KSort('KCell')]),
                    [KApply('<k>', [KSequence()]), KVariable('X', sort=KSort('KCell'))],
                ),
            ),
            (
                'ml-equals',
                KSort('GeneratedTopCell'),
                Equals(
                    SortApp('SortBool'),
                    SortApp('SortGeneratedTopCell'),
                    EVar('VarX', SortApp('SortBool')),
                    DV(SortApp('SortBool'), String('true')),
                ),
                KApply(
                    KLabel('#Equals', [KSort('Bool'), KSort('GeneratedTopCell')]),
                    [KVariable('X', sort=KSort('Bool')), TRUE],
                ),
            ),
            (
                'ml-ceil',
                KSort('GeneratedTopCell'),
                Ceil(
                    SortApp('SortBool'),
                    SortApp('SortGeneratedTopCell'),
                    EVar('VarX', SortApp('SortBool')),
                ),
                KApply(
                    KLabel('#Ceil', [KSort('Bool'), KSort('GeneratedTopCell')]),
                    [KVariable('X', sort=KSort('Bool'))],
                ),
            ),
            (
                'simple-injection',
                KSort('Foo'),
                App('Lblfoo', [], [App('inj', [SortApp('SortBaz'), SortApp('SortBar')], [App('Lblbaz', [], [])])]),
                KApply('foo', [KApply('baz')]),
            ),
            (
                'cells-conversion',
                KSort('KItem'),
                App(
                    'inj',
                    [SortApp('SortKCell'), SortApp('SortKItem')],
                    [App("Lbl'-LT-'k'-GT-'", [], [App('dotk', [], [])])],
                ),
                KApply('<k>', [KSequence()]),
            ),
            (
                'munging-problem',
                KSort('Baz'),
                App("Lblfoo-bar'Unds'SIMPLE-PROOFS'Unds'Baz", [], []),
                KApply('foo-bar_SIMPLE-PROOFS_Baz', []),
            ),
            (
                'kseq-empty',
                KSort('K'),
                App('dotk', [], []),
                KSequence([]),
            ),
            (
                'kseq-singleton',
                KSort('K'),
                App(
                    'kseq',
                    [],
                    [
                        App(
                            'inj',
                            [SortApp('SortBaz'), SortApp('SortKItem')],
                            [App("Lblfoo-bar'Unds'SIMPLE-PROOFS'Unds'Baz", [], [])],
                        ),
                        App('dotk', (), ()),
                    ],
                ),
                KSequence([KApply('foo-bar_SIMPLE-PROOFS_Baz')]),
            ),
            (
                'kseq-two-element',
                KSort('K'),
                App(
                    'kseq',
                    [],
                    [
                        App("Lblfoo'Unds'SIMPLE-PROOFS'Unds'KItem", [], []),
                        App(
                            'kseq',
                            [],
                            [
                                App(
                                    'inj',
                                    [SortApp('SortBaz'), SortApp('SortKItem')],
                                    [App("Lblfoo-bar'Unds'SIMPLE-PROOFS'Unds'Baz", [], [])],
                                ),
                                App('dotk', (), ()),
                            ],
                        ),
                    ],
                ),
                KSequence([KApply('foo_SIMPLE-PROOFS_KItem'), KApply('foo-bar_SIMPLE-PROOFS_Baz')]),
            ),
        )
        for name, sort, kore, kast in kore_kast_pairs:
            with self.subTest(name):
                kore_actual = self.kprove.kast_to_kore(kast, sort=sort)
                kast_actual = self.kprove.kore_to_kast(kore)
                self.assertEqual(kore_actual, kore)
                self.assertEqual(kast_actual, kast)

    def test_kast_to_kore(self) -> None:
        kore_kast_pairs = (
            (
                'variable-without-sort',
                KSort('Bar'),
                EVar('VarX', SortApp('SortBar')),
                KVariable('X'),
            ),
            (
                'variable-different-sorts',
                KSort('BarHolder'),
                App(
                    'Lblbarholder',
                    [],
                    [
                        App(
                            'Lblfoo',
                            [],
                            [App('inj', [SortApp('SortBaz'), SortApp('SortBar')], [EVar('VarB', SortApp('SortBaz'))])],
                        ),
                        App('inj', [SortApp('SortBaz'), SortApp('SortBar')], [EVar('VarB', SortApp('SortBaz'))]),
                    ],
                ),
                KApply('barholder', [KApply('foo', [KVariable('B', sort=KSort('Baz'))]), KVariable('B')]),
            ),
        )
        for name, sort, kore, kast in kore_kast_pairs:
            with self.subTest(name):
                kore_actual = self.kprove.kast_to_kore(kast, sort=sort)
                self.assertEqual(kore_actual, kore)
