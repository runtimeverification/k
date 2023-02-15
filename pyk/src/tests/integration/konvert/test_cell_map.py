from pathlib import Path
from typing import Final

import pytest

from pyk.kast.inner import KApply, KInner, KSort, KVariable
from pyk.konvert import kast_to_kore
from pyk.kore.kompiled import KompiledKore
from pyk.kore.prelude import int_dv
from pyk.kore.syntax import DV, App, EVar, LeftAssoc, Pattern, SortApp, String
from pyk.ktool.kprint import KPrint
from pyk.prelude.kint import INT, intToken

from ..utils import KPrintTest

BIDIRECTIONAL_TEST_DATA: Final = (
    (
        'domain-value-int',
        INT,
        int_dv(3),
        intToken(3),
    ),
    (
        'account-cell-map',
        KSort('AccountsCell'),
        App(
            "Lbl'-LT-'accounts'-GT-'",
            [],
            [
                App(
                    "Lbl'Unds'AccountCellMap'Unds'",
                    [],
                    [
                        App(
                            'LblAccountCellMapItem',
                            [],
                            [
                                App(
                                    "Lbl'-LT-'id'-GT-'",
                                    [],
                                    [DV(SortApp('SortInt'), String('3'))],
                                ),
                                App(
                                    "Lbl'-LT-'account'-GT-'",
                                    [],
                                    [
                                        App(
                                            "Lbl'-LT-'id'-GT-'",
                                            [],
                                            [DV(SortApp('SortInt'), String('3'))],
                                        ),
                                        App(
                                            "Lbl'-LT-'balance'-GT-'",
                                            [],
                                            [DV(SortApp('SortInt'), String('0'))],
                                        ),
                                    ],
                                ),
                            ],
                        ),
                        EVar("Var'Unds'DotVar2", SortApp('SortAccountCellMap')),
                    ],
                ),
            ],
        ),
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

KAST_TO_KORE_TEST_DATA: Final = (
    (
        'variable-without-sort',
        KSort('Bar'),
        EVar('VarX', SortApp('SortBar')),
        KVariable('X'),
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
)


class TestKonvertCellMap(KPrintTest):
    KOMPILE_MAIN_FILE = 'k-files/cell-map.k'

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
