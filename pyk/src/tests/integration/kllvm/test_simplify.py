from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

import pyk.kllvm.load  # noqa: F401
from pyk.kllvm import parser
from pyk.testing import RuntimeTest

from ..utils import K_FILES

if TYPE_CHECKING:
    from pyk.kllvm.runtime import Runtime


SIMPLIFY_TEST_DATA = (
    ('literal', r'\dv{SortInt{}}("0")', r'\dv{SortInt{}}("0")'),
    (
        'plus',
        r"""Lbl'UndsPlus'Int'Unds'{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("2"))""",
        r'\dv{SortInt{}}("3")',
    ),
)

SIMPLIFY_BOOL_TEST_DATA = (
    ('true', r'\dv{SortBool{}}("true")', True),
    ('false', r'\dv{SortBool{}}("false")', False),
    ('true andBool false', r"""Lbl'Unds'andBool'Unds'{}(\dv{SortBool{}}("true"), \dv{SortBool{}}("false"))""", False),
    ('false orBool true', r"""Lbl'Unds'orBool'Unds'{}(\dv{SortBool{}}("false"), \dv{SortBool{}}("true"))""", True),
)


class TestSimplify(RuntimeTest):
    KOMPILE_MAIN_FILE = K_FILES / 'imp.k'

    @pytest.mark.parametrize(
        'test_id,pattern_text,expected',
        SIMPLIFY_TEST_DATA,
        ids=[test_id for test_id, *_ in SIMPLIFY_TEST_DATA],
    )
    def test_simplify(self, runtime: Runtime, test_id: str, pattern_text: str, expected: str) -> None:
        # Given
        pattern = parser.parse_pattern(pattern_text)
        sort = parser.parse_sort('SortInt{}')

        # When
        simplified = runtime.simplify(pattern, sort)

        # Then
        assert str(simplified) == expected

    @pytest.mark.parametrize(
        'test_id,pattern_text,expected',
        SIMPLIFY_BOOL_TEST_DATA,
        ids=[test_id for test_id, *_ in SIMPLIFY_BOOL_TEST_DATA],
    )
    def test_simplify_bool(self, runtime: Runtime, test_id: str, pattern_text: str, expected: bool) -> None:
        # Given
        pattern = parser.parse_pattern(pattern_text)

        # When
        actual = runtime.simplify_bool(pattern)

        # Then
        assert actual == expected
