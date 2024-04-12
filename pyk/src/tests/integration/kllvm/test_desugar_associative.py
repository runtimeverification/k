from __future__ import annotations

from itertools import count
from typing import TYPE_CHECKING

import pytest

import pyk.kllvm.load  # noqa: F401
from pyk.kllvm.convert import pattern_to_llvm
from pyk.kore.parser import KoreParser

if TYPE_CHECKING:
    from typing import Final


TEST_DATA: Final = (
    ('a{}()', 'a{}()'),
    (r'\left-assoc{}(a{}(b0{}()))', 'b0{}()'),
    (r'\left-assoc{}(a{}(b0{}(),b1{}()))', 'a{}(b0{}(),b1{}())'),
    (r'\left-assoc{}(a{}(b0{}(),b1{}(),b2{}()))', 'a{}(a{}(b0{}(),b1{}()),b2{}())'),
    (r'\right-assoc{}(a{}(b0{}()))', 'b0{}()'),
    (r'\right-assoc{}(a{}(b0{}(),b1{}()))', 'a{}(b0{}(),b1{}())'),
    (r'\right-assoc{}(a{}(b0{}(),b1{}(),b2{}()))', 'a{}(b0{}(),a{}(b1{}(),b2{}()))'),
    (r'c{}(\left-assoc{}(a{}(b0{}(),b1{}(),b2{}())))', 'c{}(a{}(a{}(b0{}(),b1{}()),b2{}()))'),
    (r'c{}(\right-assoc{}(a{}(b0{}(),b1{}(),b2{}())))', 'c{}(a{}(b0{}(),a{}(b1{}(),b2{}())))'),
    (r'\right-assoc{}(c{}(\left-assoc{}(a{}(b0{}(),b1{}(),b2{}()))))', 'a{}(a{}(b0{}(),b1{}()),b2{}())'),
    (r'\left-assoc{}(c{}(\right-assoc{}(a{}(b0{}(),b1{}(),b2{}()))))', 'a{}(b0{}(),a{}(b1{}(),b2{}()))'),
    (
        r'\right-assoc{}(c{}(\left-assoc{}(a{}(b0{}(),b1{}(),b2{}())),d0{}(),d1{}()))',
        'c{}(a{}(a{}(b0{}(),b1{}()),b2{}()),c{}(d0{}(),d1{}()))',
    ),
    (
        r'\left-assoc{}(c{}(\right-assoc{}(a{}(b0{}(),b1{}(),b2{}())),d0{}(),d1{}()))',
        'c{}(c{}(a{}(b0{}(),a{}(b1{}(),b2{}())),d0{}()),d1{}())',
    ),
)


@pytest.mark.parametrize('kore_text,expected_text', TEST_DATA, ids=count())
def test_desugar_associative(kore_text: str, expected_text: str) -> None:
    # Given
    kore = pattern_to_llvm(KoreParser(kore_text).pattern())
    expected = pattern_to_llvm(KoreParser(expected_text).pattern())

    # When
    actual = kore.desugar_associative()

    # Then
    assert str(actual) == str(expected)
