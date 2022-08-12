from typing import Final, List, Tuple
from unittest import TestCase

from pyk.kore.lexer import KoreLexer, KoreToken

# Abbreviate for convenience
TT = KoreToken.Type


class LexerTest(TestCase):
    def test_lexer_success(self):
        # Given
        TEST_DATA: Final[Tuple[Tuple[str, List[KoreToken.Type]], ...]] = (
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

        for i, (text, expected) in enumerate(TEST_DATA):
            with self.subTest(i=i):
                # When
                actual = [token.type for token in KoreLexer(text)]

                # Then
                self.assertListEqual(actual, expected + [TT.EOF])

    def test_lexer_failure(self):
        # Given
        TEST_DATA: Final[Tuple[str, ...]] = ('-a', "'a", '*', '/*', '\\', '@', '\\@')

        for i, text in enumerate(TEST_DATA):
            with self.subTest(i=i):
                # Then
                with self.assertRaises(ValueError):
                    [token for token in KoreLexer(text)]
