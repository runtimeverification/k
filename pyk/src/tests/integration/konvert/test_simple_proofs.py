from pathlib import Path
from typing import Final

import pytest

from pyk.kast.inner import KApply, KInner, KLabel, KSequence, KSort, KToken, KVariable
from pyk.konvert import kast_to_kore
from pyk.kore.kompiled import KompiledKore
from pyk.kore.prelude import BOOL as KORE_BOOL
from pyk.kore.prelude import BYTES as KORE_BYTES
from pyk.kore.prelude import INT as KORE_INT
from pyk.kore.prelude import bool_dv, int_dv, string_dv
from pyk.kore.syntax import (
    DV,
    And,
    App,
    Bottom,
    Ceil,
    Equals,
    EVar,
    Exists,
    Implies,
    LeftAssoc,
    Not,
    Pattern,
    RightAssoc,
    SortApp,
    String,
    Top,
)
from pyk.ktool import KPrint
from pyk.prelude.bytes import bytesToken
from pyk.prelude.kbool import TRUE
from pyk.prelude.kint import INT, intToken
from pyk.prelude.ml import mlBottom, mlImplies, mlTop
from pyk.prelude.string import STRING, stringToken

from ..utils import KPrintTest

BIDIRECTIONAL_TEST_DATA: Final = (
    (
        'domain-value-int',
        INT,
        int_dv(3),
        intToken(3),
    ),
    (
        'domain-value-string',
        STRING,
        string_dv('foobar\n'),
        stringToken('foobar\n'),
    ),
    (
        'domain-value-bytes',
        KSort('Bytes'),
        DV(KORE_BYTES, String(chr(0) + chr(60) + chr(96) + chr(245))),
        bytesToken(chr(0) + chr(60) + chr(96) + chr(245)),
    ),
    (
        'domain-value-other',
        KSort('Foo'),
        DV(SortApp('SortFoo'), String('hello\\n')),
        KToken('hello\\n', 'Foo'),
    ),
    (
        'ml-top',
        KSort('GeneratedTopCell'),
        Top(SortApp('SortGeneratedTopCell')),
        mlTop(),
    ),
    (
        'ml-bottom',
        KSort('GeneratedTopCell'),
        Bottom(SortApp('SortGeneratedTopCell')),
        mlBottom(),
    ),
    (
        'ml-implies',
        KSort('GeneratedTopCell'),
        Implies(
            SortApp('SortGeneratedTopCell'),
            EVar('VarX', SortApp('SortGeneratedTopCell')),
            EVar('VarY', SortApp('SortGeneratedTopCell')),
        ),
        mlImplies(
            KVariable('X', sort=KSort('GeneratedTopCell')),
            KVariable('Y', sort=KSort('GeneratedTopCell')),
            sort=KSort('GeneratedTopCell'),
        ),
    ),
    (
        'variable-with-sort',
        INT,
        EVar('VarX', KORE_INT),
        KVariable('X', sort=INT),
    ),
    (
        'variable-with-super-sort',
        KSort('Bar'),
        App('inj', [SortApp('SortBaz'), SortApp('SortBar')], [EVar('VarX', SortApp('SortBaz'))]),
        KVariable('X', sort=KSort('Baz')),
    ),
    (
        'variable-with-underscore',
        INT,
        EVar("VarX'Unds'Y", KORE_INT),
        KVariable('X_Y', sort=INT),
    ),
    (
        'issue:k/2762',
        KSort('Bool'),
        App('Lblpred1', [], [int_dv(3)]),
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
            KORE_BOOL,
            SortApp('SortGeneratedTopCell'),
            EVar('VarX', KORE_BOOL),
            bool_dv(True),
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
            KORE_BOOL,
            SortApp('SortGeneratedTopCell'),
            EVar('VarX', KORE_BOOL),
        ),
        KApply(
            KLabel('#Ceil', [KSort('Bool'), KSort('GeneratedTopCell')]),
            [KVariable('X', sort=KSort('Bool'))],
        ),
    ),
    (
        'ml-exists',
        KSort('Bool'),
        Exists(
            KORE_BOOL,
            EVar('VarX', KORE_BOOL),
            EVar('VarX', KORE_BOOL),
        ),
        KApply(
            KLabel('#Exists', [KSort('Bool')]),
            [
                KVariable('X', sort=KSort('Bool')),
                KVariable('X', sort=KSort('Bool')),
            ],
        ),
    ),
    (
        'ml-not',
        KSort('Bool'),
        Not(
            KORE_BOOL,
            EVar('VarX', KORE_BOOL),
        ),
        KApply(
            KLabel('#Not', [KSort('Bool')]),
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
    (
        'if-then-else',
        KSort('K'),
        App(
            "Lbl'Hash'if'UndsHash'then'UndsHash'else'UndsHash'fi'Unds'K-EQUAL-SYNTAX'Unds'Sort'Unds'Bool'Unds'Sort'Unds'Sort",
            [SortApp('SortK')],
            [EVar('VarC', KORE_BOOL), EVar('VarB1', SortApp('SortK')), EVar('VarB2', SortApp('SortK'))],
        ),
        KApply(
            KLabel('#if_#then_#else_#fi_K-EQUAL-SYNTAX_Sort_Bool_Sort_Sort', [KSort('K')]),
            [
                KVariable('C', sort=KSort('Bool')),
                KVariable('B1', sort=KSort('K')),
                KVariable('B2', sort=KSort('K')),
            ],
        ),
    ),
)

KAST_TO_KORE_TEST_DATA: Final = (
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
    (
        'variable-with-multi-sort',
        KSort('BarHolder'),
        App(
            'Lblbarholder2',
            [],
            [
                App('inj', [SortApp('SortBaz'), SortApp('SortBar')], [EVar('VarX', SortApp('SortBaz'))]),
                EVar('VarX', SortApp('SortBaz')),
            ],
        ),
        KApply('barholder2', [KVariable('X', sort=KSort('Baz')), KVariable('X', sort=KSort('Bar'))]),
    ),
    (
        'ml-exists-var-inference',
        KSort('Foo'),
        Exists(
            SortApp('SortFoo'),
            EVar('VarX', SortApp('SortBar')),
            App('Lblfoo', [], [EVar('VarX', SortApp('SortBar'))]),
        ),
        KApply(KLabel('#Exists', [KSort('Foo')]), [KVariable('X'), KApply('foo', [KVariable('X')])]),
    ),
    (
        'ksequence-empty',
        KSort('K'),
        App('dotk', [], []),
        KSequence([]),
    ),
    (
        'ksequence-singleton-var',
        KSort('K'),
        EVar('VarCONT', SortApp('SortK')),
        KSequence([KVariable('CONT')]),
    ),
    (
        'ksequence-duo-var-1',
        KSort('K'),
        App(
            'kseq',
            (),
            [
                EVar('VarELEM', SortApp('SortKItem')),
                EVar('VarCONT', SortApp('SortK')),
            ],
        ),
        KSequence([KVariable('ELEM'), KVariable('CONT')]),
    ),
    (
        'ksequence-duo-var-2',
        KSort('K'),
        App(
            'kseq',
            (),
            [
                EVar('VarELEM1', SortApp('SortKItem')),
                App('kseq', (), [EVar('VarELEM2', SortApp('SortKItem')), App('dotk', (), ())]),
            ],
        ),
        KSequence([KVariable('ELEM1', sort=KSort('KItem')), KVariable('ELEM2', sort=KSort('KItem'))]),
    ),
)

KORE_TO_KAST_TEST_DATA: Final = (
    (
        'left-assoc',
        KSort('Map'),
        LeftAssoc(
            App(
                "Lbl'Unds'Map'Unds'",
                [],
                [
                    EVar('VarX', SortApp('SortMap')),
                    EVar('VarY', SortApp('SortMap')),
                    EVar('VarZ', SortApp('SortMap')),
                ],
            )
        ),
        KApply(
            '_Map_',
            [
                KApply('_Map_', [KVariable('X', sort=KSort('Map')), KVariable('Y', sort=KSort('Map'))]),
                KVariable('Z', sort=KSort('Map')),
            ],
        ),
    ),
    (
        'right-assoc',
        KSort('Map'),
        RightAssoc(
            App(
                "Lbl'Unds'Map'Unds'",
                [],
                [
                    EVar('VarX', SortApp('SortMap')),
                    EVar('VarY', SortApp('SortMap')),
                    EVar('VarZ', SortApp('SortMap')),
                ],
            )
        ),
        KApply(
            '_Map_',
            [
                KVariable('X', sort=KSort('Map')),
                KApply('_Map_', [KVariable('Y', sort=KSort('Map')), KVariable('Z', sort=KSort('Map'))]),
            ],
        ),
    ),
)


class TestKonvertSimpleProofs(KPrintTest):
    KOMPILE_MAIN_FILE = 'k-files/simple-proofs.k'

    @pytest.fixture(scope='class')
    def kompiled_kore(self, definition_dir: Path) -> KompiledKore:
        return KompiledKore(definition_dir)

    @pytest.mark.parametrize(
        'test_id,sort,kore,kast', BIDIRECTIONAL_TEST_DATA, ids=[test_id for test_id, *_ in BIDIRECTIONAL_TEST_DATA]
    )
    def test_bidirectional(
        self,
        kprint: KPrint,
        kompiled_kore: KompiledKore,
        test_id: str,
        sort: KSort,
        kore: Pattern,
        kast: KInner,
    ) -> None:
        # When
        actual_kore = kast_to_kore(kprint.definition, kompiled_kore, kast, sort=sort)
        actual_kast = kprint.kore_to_kast(kore)

        # Then
        assert actual_kore == kore
        assert actual_kast == kast

    @pytest.mark.parametrize(
        'test_id,sort,kore,kast', KAST_TO_KORE_TEST_DATA, ids=[test_id for test_id, *_ in KAST_TO_KORE_TEST_DATA]
    )
    def test_kast_to_kore(
        self,
        kprint: KPrint,
        kompiled_kore: KompiledKore,
        test_id: str,
        sort: KSort,
        kore: Pattern,
        kast: KInner,
    ) -> None:
        # When
        actual_kore = kast_to_kore(kprint.definition, kompiled_kore, kast, sort=sort)

        # Then
        assert actual_kore == kore

    @pytest.mark.parametrize(
        'test_id,_sort,kore,kast', KORE_TO_KAST_TEST_DATA, ids=[test_id for test_id, *_ in KORE_TO_KAST_TEST_DATA]
    )
    def test_kore_to_kast(self, kprint: KPrint, test_id: str, _sort: KSort, kore: Pattern, kast: KInner) -> None:
        # When
        actual_kast = kprint.kore_to_kast(kore)

        # Then
        assert actual_kast == kast
