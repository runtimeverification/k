from __future__ import annotations

from itertools import count
from typing import TYPE_CHECKING, Final

import pytest

from pyk.utils import POSet, deconstruct_short_hash

if TYPE_CHECKING:
    from collections.abc import Iterable


FULL_HASH: Final = '0001000200030004000500060007000800010002000300040005000600070008'
TEST_DATA_PASS: Final = (
    ('..abcdef', ('', 'abcdef')),
    ('abcdef..', ('abcdef', '')),
    ('abcdef..12345', ('abcdef', '12345')),
    (FULL_HASH, (FULL_HASH, FULL_HASH)),
)


@pytest.mark.parametrize('short_hash,expected', TEST_DATA_PASS, ids=[short_hash for short_hash, _ in TEST_DATA_PASS])
def test_deconstruct_short_hash_pass(short_hash: str, expected: tuple[str, str]) -> None:
    # When
    actual = deconstruct_short_hash(short_hash)

    # Then
    assert actual == expected


@pytest.mark.parametrize('short_hash', ('3.c62e73544.', '3..XXX', '3...adf'))
def test_deconstruct_short_hash_fail(short_hash: str) -> None:
    with pytest.raises(ValueError) as excinfo:
        # When
        deconstruct_short_hash(short_hash)

    # Then
    assert str(excinfo.value) == f'Bad short hash: {short_hash}'


POSET_TEST_DATA: Final[tuple[tuple[tuple[tuple[int, int], ...], dict[int, set[int]]], ...]] = (
    ((), {}),
    (((1, 2),), {1: {2}}),
    (((1, 2), (1, 3)), {1: {2, 3}}),
    (((1, 2), (3, 4)), {1: {2}, 3: {4}}),
    (((1, 2), (2, 3)), {1: {2, 3}, 2: {3}}),
    (((1, 2), (2, 3), (3, 4)), {1: {2, 3, 4}, 2: {3, 4}, 3: {4}}),
    (((1, 2), (2, 1)), {1: {1, 2}, 2: {1, 2}}),  # Not antisymmetric
)


@pytest.mark.parametrize('relation,expected', POSET_TEST_DATA, ids=count())
def test_poset(relation: Iterable[tuple[int, int]], expected: dict[int, set[int]]) -> None:
    # When
    image = POSet(relation).image
    actual = {x: set(ys) for x, ys in image.items()}

    # Then
    assert actual == expected
