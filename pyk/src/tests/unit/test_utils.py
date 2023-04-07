from typing import Final

import pytest

from pyk.utils import deconstruct_short_hash

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
