import pytest

from pyk.kore.syntax import check_id, check_set_var_id, check_symbol_id
from pyk.utils import raised

BASE_TEST_DATA = (
    ('', False),
    ('-', False),
    ("'", False),
    ('0', False),
    ('@', False),
    ('a', True),
    ('A', True),
    ('a0', True),
    ('a-', True),
    ("a'", True),
)

ID_TEST_DATA = BASE_TEST_DATA + (('sort', False),)


@pytest.mark.parametrize('s,expected', ID_TEST_DATA, ids=[s for s, _ in ID_TEST_DATA])
def test_is_id(s: str, expected: bool) -> None:
    # When
    actual = not raised(check_id, s)

    # Then
    assert actual == expected


SYMBOL_ID_TEST_DATA = ID_TEST_DATA + tuple(('\\' + s, expected) for s, expected in BASE_TEST_DATA) + (('\\sort', True),)


@pytest.mark.parametrize('s,expected', SYMBOL_ID_TEST_DATA, ids=[s for s, _ in SYMBOL_ID_TEST_DATA])
def test_is_symbol_id(s: str, expected: bool) -> None:
    # When
    actual = not raised(check_symbol_id, s)

    # Then
    assert actual == expected


SET_VARIABLE_ID_TEST_DATA = (
    tuple(('@' + s, expected) for s, expected in BASE_TEST_DATA)
    + tuple((s, False) for s, _ in ID_TEST_DATA)
    + (('@sort', True),)
)


@pytest.mark.parametrize('s,expected', SET_VARIABLE_ID_TEST_DATA, ids=[s for s, _ in SET_VARIABLE_ID_TEST_DATA])
def test_is_set_variable_id(s: str, expected: bool) -> None:
    # When
    actual = not raised(check_set_var_id, s)

    # Then
    assert actual == expected
