from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

import pyk.kllvm.load  # noqa: F401
from pyk.kllvm import parser
from pyk.testing import RuntimeTest

from ..utils import K_FILES

if TYPE_CHECKING:
    from pyk.kllvm.runtime import Runtime


EVALUATE_TEST_DATA = (
    ('1 + 2', r"""Lbl'UndsPlus'Int'Unds'{}(\dv{SortInt{}}("1"),\dv{SortInt{}}("2"))""", r'\dv{SortInt{}}("3")'),
    ('1 * 2', r"""Lbl'UndsStar'Int'Unds'{}(\dv{SortInt{}}("1"),\dv{SortInt{}}("2"))""", r'\dv{SortInt{}}("2")'),
    (
        '1 + (2 * 3)',
        r"""
        Lbl'UndsPlus'Int'Unds'{}(
            \dv{SortInt{}}("1"),
            Lbl'UndsStar'Int'Unds'{}(\dv{SortInt{}}("2"), \dv{SortInt{}}("3"))
        )
        """,
        r'\dv{SortInt{}}("7")',
    ),
)


class TestEvaluate(RuntimeTest):
    KOMPILE_MAIN_FILE = K_FILES / 'imp.k'

    @pytest.mark.parametrize(
        'test_id,pattern_text,expected',
        EVALUATE_TEST_DATA,
        ids=[test_id for test_id, *_ in EVALUATE_TEST_DATA],
    )
    def test_simplify(self, runtime: Runtime, test_id: str, pattern_text: str, expected: str) -> None:
        # Given
        pattern = parser.parse_pattern(pattern_text)

        # When
        actual = runtime.evaluate(pattern)

        # Then
        assert str(actual) == expected
