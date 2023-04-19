from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kore.prelude import (
    INT,
    SORT_K_ITEM,
    generated_counter,
    generated_top,
    inj,
    int_dv,
    k,
    kseq,
    top_cell_initializer,
)
from pyk.kore.syntax import App
from pyk.ktool.krun import KRun

if TYPE_CHECKING:
    from collections.abc import Mapping
    from pathlib import Path

    from pyk.kore.syntax import Pattern

    from ..utils import Kompiler


@pytest.fixture(scope='module')
def definition_dir(kompile: Kompiler) -> Path:
    return kompile('k-files/top-cell-initializer.k')


def test_top_cell_initializer(definition_dir: Path) -> None:
    # Given
    config = {
        '$PGM': 0,
        '$A': 1,
        '$B': 2,
        '$C': 3,
    }

    expected = _expected(config)
    krun = KRun(definition_dir)

    # When
    init_config = top_cell_initializer(_input_config(config))
    actual = krun.run_kore_term(init_config)

    # Then
    assert actual == expected


def _input_config(config: Mapping[str, int]) -> dict[str, Pattern]:
    return {key: inj(INT, SORT_K_ITEM, int_dv(value)) for key, value in config.items()}


def _expected(config: Mapping[str, int]) -> Pattern:
    return generated_top(
        (
            k(kseq((inj(INT, SORT_K_ITEM, int_dv(config['$PGM'])),)).pattern),
            App("Lbl'-LT-'a'-GT-'", (), (int_dv(config['$A']),)),
            App("Lbl'-LT-'b'-GT-'", (), (int_dv(config['$B']),)),
            generated_counter(int_dv(0)),
            App("Lbl'-LT-'c'-GT-'", (), (int_dv(config['$C']),)),
        )
    )
