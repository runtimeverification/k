from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kast.inner import KApply, KSequence, KToken, KVariable
from pyk.kast.parser import KAstParser

if TYPE_CHECKING:
    from typing import Final

    from pyk.kast import KInner


TEST_DATA: Final = (
    ('_', KVariable('_')),
    ('X', KVariable('X')),
    ('#token("1", "Int")', KToken('1', 'Int')),
    (r'#token("\"foo\"", "String")', KToken('"foo"', 'String')),
    ('.K', KSequence()),
    ('foo(.KList)', KApply('foo')),
    ('`_+_`(#token("1", "Int"), X)', KApply('_+_', KToken('1', 'Int'), KVariable('X'))),
    (r'`\``(.KList)', KApply('`')),
    (r'`_\\_`(.KList)', KApply(r'_\_')),
    ('`<k>`(foo(.KList)~>bar(.KList))', KApply('<k>', KSequence(KApply('foo'), KApply('bar')))),
)


@pytest.mark.parametrize('text,expected', TEST_DATA, ids=[text for text, _ in TEST_DATA])
def test_parser(text: str, expected: KInner) -> None:
    # Given
    parser = KAstParser(text)

    # When
    actual = parser.k()

    # Then
    assert actual == expected
