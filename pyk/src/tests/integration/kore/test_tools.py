from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kore.parser import KoreParser
from pyk.kore.tools import PrintOutput, kore_print

from ..utils import K_FILES

if TYPE_CHECKING:
    from pathlib import Path

    from pyk.testing import Kompiler


@pytest.fixture(scope='module')
def imp_kompiled(kompile: Kompiler) -> Path:
    return kompile(main_file=K_FILES / 'imp.k')


KORE_PRINT_TEST_DATA = (
    (r'\top{SortInt{}}()', '#Top'),
    (r'\dv{SortInt{}}("1")', '1'),
    (r"Lbl'-LT-'k'-GT-'{}(dotk{}())", '<k>\n  .\n</k>'),
)


@pytest.mark.parametrize(
    'kore_text,expected',
    KORE_PRINT_TEST_DATA,
    ids=[kore_text for kore_text, _ in KORE_PRINT_TEST_DATA],
)
def test_kore_print(imp_kompiled: Path, kore_text: str, expected: str) -> None:
    # Given
    pattern = KoreParser(kore_text).pattern()

    # When
    actual = kore_print(pattern, definition_dir=imp_kompiled, output=PrintOutput.PRETTY)

    # Then
    assert actual == expected
