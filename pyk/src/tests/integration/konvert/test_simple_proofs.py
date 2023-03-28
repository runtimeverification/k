from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kast.inner import KApply, KLabel, KSequence, KSort, KToken, KVariable
from pyk.konvert import kast_to_kore
from pyk.kore.kompiled import KompiledKore
from pyk.kore.parser import KoreParser
from pyk.prelude.bytes import bytesToken
from pyk.prelude.kbool import TRUE
from pyk.prelude.kint import INT, intToken
from pyk.prelude.ml import mlBottom, mlImplies, mlTop
from pyk.prelude.string import STRING, stringToken

from ..utils import KPrintTest

if TYPE_CHECKING:
    from pathlib import Path
    from typing import Final

    from pyk.kast import KInner
    from pyk.ktool.kprint import KPrint


BIDIRECTIONAL_TEST_DATA: Final = (
    (
        'domain-value-int',
        INT,
        r'\dv{SortInt{}}("3")',
        intToken(3),
    ),
    (
        'domain-value-string',
        STRING,
        r'\dv{SortString{}}("foobar\n")',
        stringToken('foobar\n'),
    ),
    (
        'domain-value-bytes',
        KSort('Bytes'),
        r'\dv{SortBytes{}}("\x00<`\xf5")',
        bytesToken(chr(0) + chr(60) + chr(96) + chr(245)),
    ),
    (
        'domain-value-other',
        KSort('Foo'),
        r'\dv{SortFoo{}}("hello\\n")',
        KToken('hello\\n', 'Foo'),
    ),
    (
        'ml-top',
        KSort('GeneratedTopCell'),
        r'\top{SortGeneratedTopCell{}}()',
        mlTop(),
    ),
    (
        'ml-bottom',
        KSort('GeneratedTopCell'),
        r'\bottom{SortGeneratedTopCell{}}()',
        mlBottom(),
    ),
    (
        'ml-implies',
        KSort('GeneratedTopCell'),
        r"""
        \implies{SortGeneratedTopCell{}}(
            VarX : SortGeneratedTopCell{},
            VarY : SortGeneratedTopCell{}
        )
        """,
        mlImplies(
            KVariable('X', sort=KSort('GeneratedTopCell')),
            KVariable('Y', sort=KSort('GeneratedTopCell')),
            sort=KSort('GeneratedTopCell'),
        ),
    ),
    (
        'variable-with-sort',
        INT,
        'VarX : SortInt{}',
        KVariable('X', sort=INT),
    ),
    (
        'variable-with-super-sort',
        KSort('Bar'),
        'inj{SortBaz{}, SortBar{}}(VarX : SortBaz{})',
        KVariable('X', sort=KSort('Baz')),
    ),
    (
        'variable-with-underscore',
        INT,
        "VarX'Unds'Y : SortInt{}",
        KVariable('X_Y', sort=INT),
    ),
    (
        'issue:k/2762',
        KSort('Bool'),
        r'Lblpred1{}(\dv{SortInt{}}("3"))',
        KApply('pred1', [intToken(3)]),
    ),
    (
        'cells-conversion',
        KSort('KCell'),
        "Lbl'-LT-'k'-GT-'{}(dotk{}())",
        KApply('<k>', [KSequence()]),
    ),
    (
        'constrained-term',
        KSort('KCell'),
        r"""
        \and{SortKCell{}}(
            Lbl'-LT-'k'-GT-'{}(dotk{}()),
            VarX : SortKCell{}
        )
        """,
        KApply(
            KLabel('#And', params=[KSort('KCell')]),
            [KApply('<k>', [KSequence()]), KVariable('X', sort=KSort('KCell'))],
        ),
    ),
    (
        'ml-equals',
        KSort('GeneratedTopCell'),
        r"""
        \equals{SortBool{}, SortGeneratedTopCell{}}(
            VarX : SortBool{},
            \dv{SortBool{}}("true")
        )
        """,
        KApply(
            KLabel('#Equals', [KSort('Bool'), KSort('GeneratedTopCell')]),
            [KVariable('X', sort=KSort('Bool')), TRUE],
        ),
    ),
    (
        'ml-ceil',
        KSort('GeneratedTopCell'),
        r'\ceil{SortBool{}, SortGeneratedTopCell{}}(VarX : SortBool{})',
        KApply(
            KLabel('#Ceil', [KSort('Bool'), KSort('GeneratedTopCell')]),
            [KVariable('X', sort=KSort('Bool'))],
        ),
    ),
    (
        'ml-exists',
        KSort('Bool'),
        r'\exists{SortBool{}}(VarX : SortBool{}, VarX : SortBool{})',
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
        r'\not{SortBool{}}(VarX : SortBool{})',
        KApply(
            KLabel('#Not', [KSort('Bool')]),
            [KVariable('X', sort=KSort('Bool'))],
        ),
    ),
    (
        'simple-injection',
        KSort('Foo'),
        'Lblfoo{}(inj{SortBaz{}, SortBar{}}(Lblbaz{}()))',
        KApply('foo', [KApply('baz')]),
    ),
    (
        'cells-conversion',
        KSort('KItem'),
        "inj{SortKCell{}, SortKItem{}}(Lbl'-LT-'k'-GT-'{}(dotk{}()))",
        KApply('<k>', [KSequence()]),
    ),
    (
        'munging-problem',
        KSort('Baz'),
        r"Lblfoo-bar'Unds'SIMPLE-PROOFS'Unds'Baz{}()",
        KApply('foo-bar_SIMPLE-PROOFS_Baz', []),
    ),
    (
        'kseq-empty',
        KSort('K'),
        'dotk{}()',
        KSequence([]),
    ),
    (
        'kseq-singleton',
        KSort('K'),
        "kseq{}(inj{SortBaz{}, SortKItem{}}(Lblfoo-bar'Unds'SIMPLE-PROOFS'Unds'Baz{}()), dotk{}())",
        KSequence([KApply('foo-bar_SIMPLE-PROOFS_Baz')]),
    ),
    (
        'kseq-two-element',
        KSort('K'),
        """
        kseq{}(
            Lblfoo'Unds'SIMPLE-PROOFS'Unds'KItem{}(),
            kseq{}(
                inj{SortBaz{}, SortKItem{}}(Lblfoo-bar'Unds'SIMPLE-PROOFS'Unds'Baz{}()),
                dotk{}()
            )
        )
        """,
        KSequence([KApply('foo_SIMPLE-PROOFS_KItem'), KApply('foo-bar_SIMPLE-PROOFS_Baz')]),
    ),
    (
        'if-then-else',
        KSort('K'),
        r"""
        Lbl'Hash'if'UndsHash'then'UndsHash'else'UndsHash'fi'Unds'K-EQUAL-SYNTAX'Unds'Sort'Unds'Bool'Unds'Sort'Unds'Sort{SortK{}}(
            VarC : SortBool{}, VarB1 : SortK{}, VarB2 : SortK {}
        )
        """,
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

KAST_TO_KORE_TEST_DATA: Final = BIDIRECTIONAL_TEST_DATA + (
    (
        'variable-without-sort',
        KSort('Bar'),
        'VarX : SortBar{}',
        KVariable('X'),
    ),
    (
        'variable-different-sorts',
        KSort('BarHolder'),
        """
        Lblbarholder{}(
            Lblfoo{}(inj{SortBaz{}, SortBar{}}(VarB : SortBaz{})),
            inj{SortBaz{}, SortBar{}}(VarB : SortBaz{})
        )
        """,
        KApply('barholder', [KApply('foo', [KVariable('B', sort=KSort('Baz'))]), KVariable('B')]),
    ),
    (
        'variable-with-multi-sort',
        KSort('BarHolder'),
        'Lblbarholder2{}(inj{SortBaz{}, SortBar{}}(VarX : SortBaz{}), VarX : SortBaz{})',
        KApply('barholder2', [KVariable('X', sort=KSort('Baz')), KVariable('X', sort=KSort('Bar'))]),
    ),
    (
        'ml-exists-var-inference',
        KSort('Foo'),
        r'\exists{SortFoo{}}(VarX : SortBar{}, Lblfoo{}(VarX : SortBar{}))',
        KApply(KLabel('#Exists', [KSort('Foo')]), [KVariable('X'), KApply('foo', [KVariable('X')])]),
    ),
    (
        'ksequence-empty',
        KSort('K'),
        'dotk{}()',
        KSequence([]),
    ),
    (
        'ksequence-singleton-var',
        KSort('K'),
        'VarCONT : SortK{}',
        KSequence([KVariable('CONT')]),
    ),
    (
        'ksequence-duo-var-1',
        KSort('K'),
        'kseq{}(VarELEM : SortKItem{}, VarCONT : SortK{})',
        KSequence([KVariable('ELEM'), KVariable('CONT')]),
    ),
    (
        'ksequence-duo-var-2',
        KSort('K'),
        'kseq{}(VarELEM1 : SortKItem{}, kseq{}(VarELEM2 : SortKItem{}, dotk{}()))',
        KSequence([KVariable('ELEM1', sort=KSort('KItem')), KVariable('ELEM2', sort=KSort('KItem'))]),
    ),
)

KORE_TO_KAST_TEST_DATA: Final = BIDIRECTIONAL_TEST_DATA + (
    (
        'left-assoc',
        KSort('Map'),
        r"\left-assoc{}(Lbl'Unds'Map'Unds'{}(VarX : SortMap{}, VarY : SortMap{}, VarZ : SortMap{}))",
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
        r"\right-assoc{}(Lbl'Unds'Map'Unds'{}(VarX : SortMap{}, VarY : SortMap{}, VarZ : SortMap{}))",
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
        'test_id,sort,kore_text,kast',
        KAST_TO_KORE_TEST_DATA,
        ids=[test_id for test_id, *_ in KAST_TO_KORE_TEST_DATA],
    )
    def test_kast_to_kore(
        self,
        kprint: KPrint,
        kompiled_kore: KompiledKore,
        test_id: str,
        sort: KSort,
        kore_text: str,
        kast: KInner,
    ) -> None:
        # Given
        kore = KoreParser(kore_text).pattern()

        # When
        actual_kore = kast_to_kore(kprint.definition, kompiled_kore, kast, sort=sort)

        # Then
        assert actual_kore == kore

    @pytest.mark.parametrize(
        'test_id,_sort,kore_text,kast',
        KORE_TO_KAST_TEST_DATA,
        ids=[test_id for test_id, *_ in KORE_TO_KAST_TEST_DATA],
    )
    def test_kore_to_kast(
        self,
        kprint: KPrint,
        test_id: str,
        _sort: KSort,
        kore_text: str,
        kast: KInner,
    ) -> None:
        # Given
        kore = KoreParser(kore_text).pattern()

        # When
        actual_kast = kprint.kore_to_kast(kore)

        # Then
        assert actual_kast == kast
