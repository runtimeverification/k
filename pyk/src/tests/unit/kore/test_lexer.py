from typing import Final, List, Tuple

import pytest

from pyk.kore.lexer import KoreLexer, TokenType

# Abbreviate for convenience
TT = TokenType


PASS_TEST_DATA: Final[Tuple[Tuple[str, List[TokenType]], ...]] = (
    ('', []),
    (' ', []),
    ('//', []),
    ('/**/', []),
    ('/*///***/', []),
    ('/* comment */', []),
    ('xyz', [TT.ID]),
    ("x-y'z", [TT.ID]),
    ('   xyz\n', [TT.ID]),
    ('\\xyz', [TT.SYMBOL_ID]),
    ('@xyz', [TT.SET_VAR_ID]),
    ('module', [TT.KW_MODULE]),
    ('a b c', [TT.ID, TT.ID, TT.ID]),
    (
        'sort Map{K, V} []',
        [TT.KW_SORT, TT.ID, TT.LBRACE, TT.ID, TT.COMMA, TT.ID, TT.RBRACE, TT.LBRACK, TT.RBRACK],
    ),
)


@pytest.mark.parametrize('text,expected', PASS_TEST_DATA, ids=[text for text, _ in PASS_TEST_DATA])
def test_lexer_success(text: str, expected: List[TokenType]) -> None:
    # When
    actual = [token.type for token in KoreLexer(text)]

    # Then
    assert actual == expected + [TT.EOF]


@pytest.mark.parametrize('text', ('-a', "'a", '*', '/*', '\\', '@', '\\@'))
def test_lexer_failure(text: str) -> None:
    # Then
    with pytest.raises(ValueError):
        list(KoreLexer(text))
