from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kast.inner import KApply, KSort, KVariable
from pyk.konvert import kast_to_kore, kore_to_kast
from pyk.kore.kompiled import KompiledKore
from pyk.kore.parser import KoreParser
from pyk.prelude.kint import INT, intToken
from pyk.testing import KompiledTest

from ..utils import K_FILES

if TYPE_CHECKING:
    from pathlib import Path
    from typing import Final

    from pyk.kast import KInner
    from pyk.kast.outer import KDefinition


BIDIRECTIONAL_TEST_DATA: Final = (
    (
        'domain-value-int',
        INT,
        r'\dv{SortInt{}}("3")',
        intToken(3),
    ),
    (
        'account-cell-map',
        KSort('AccountsCell'),
        r"""
        Lbl'-LT-'accounts'-GT-'{}(
            Lbl'Unds'AccountCellMap'Unds'{}(
                LblAccountCellMapItem{}(
                    Lbl'-LT-'id'-GT-'{}(\dv{SortInt{}}("3")),
                    Lbl'-LT-'account'-GT-'{}(
                        Lbl'-LT-'id'-GT-'{}(\dv{SortInt{}}("3")),
                        Lbl'-LT-'balance'-GT-'{}(\dv{SortInt{}}("0"))
                    )
                ),
                Var'Unds'DotVar2 : SortAccountCellMap{}
            )
        )
        """,
        KApply(
            '<accounts>',
            [
                KApply(
                    '_AccountCellMap_',
                    [
                        KApply('<account>', [KApply('<id>', [intToken(3)]), KApply('<balance>', [intToken(0)])]),
                        KVariable('_DotVar2', sort=KSort('AccountCellMap')),
                    ],
                )
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
)

KORE_TO_KAST_TEST_DATA: Final = BIDIRECTIONAL_TEST_DATA + (
    (
        'left-assoc',
        KSort('Map'),
        r"""
        \left-assoc{}(
            Lbl'Unds'Map'Unds'{}(
                VarX : SortMap{},
                VarY : SortMap{},
                VarZ : SortMap{},
            )
        )
        """,
        KApply(
            '_Map_',
            [
                KApply('_Map_', [KVariable('X', sort=KSort('Map')), KVariable('Y', sort=KSort('Map'))]),
                KVariable('Z', sort=KSort('Map')),
            ],
        ),
    ),
)


class TestKonvertCellMap(KompiledTest):
    KOMPILE_MAIN_FILE = K_FILES / 'cell-map.k'

    @pytest.fixture(scope='class')
    def kompiled_kore(self, definition_dir: Path) -> KompiledKore:
        return KompiledKore.load(definition_dir)

    @pytest.mark.parametrize(
        'test_id,sort,kore_text,kast',
        KAST_TO_KORE_TEST_DATA,
        ids=[test_id for test_id, *_ in KAST_TO_KORE_TEST_DATA],
    )
    def test_kast_to_kore(
        self,
        definition: KDefinition,
        kompiled_kore: KompiledKore,
        test_id: str,
        sort: KSort,
        kore_text: str,
        kast: KInner,
    ) -> None:
        # Given
        kore = KoreParser(kore_text).pattern()

        # When
        actual_kore = kast_to_kore(definition, kompiled_kore, kast, sort=sort)

        # Then
        assert actual_kore == kore

    @pytest.mark.parametrize(
        'test_id,_sort,kore_text,kast',
        KORE_TO_KAST_TEST_DATA,
        ids=[test_id for test_id, *_ in KORE_TO_KAST_TEST_DATA],
    )
    def test_kore_to_kast(
        self,
        definition: KDefinition,
        test_id: str,
        _sort: KSort,
        kore_text: str,
        kast: KInner,
    ) -> None:
        # Given
        kore = KoreParser(kore_text).pattern()

        # When
        actual_kast = kore_to_kast(definition, kore)

        # Then
        assert actual_kast == kast
