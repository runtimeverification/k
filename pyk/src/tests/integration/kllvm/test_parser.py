from __future__ import annotations

from typing import TYPE_CHECKING

import pyk.kllvm.load  # noqa: F401
from pyk.kllvm.parser import parse_file, parse_text

if TYPE_CHECKING:
    from pathlib import Path


def test_parse_file(tmp_path: Path) -> None:
    # Given
    kore_text = 'A{}(B{}(),C{}())'
    kore_file = tmp_path / 'test.kore'
    kore_file.write_text(kore_text)

    # When
    actual = parse_file(kore_file)

    # Then
    assert str(actual) == kore_text


def test_parse_text() -> None:
    # Given
    kore_text = 'A{}(X : S,Y : Z,Int{}())'

    # When
    actual = parse_text(kore_text)

    # Then
    assert str(actual) == kore_text
