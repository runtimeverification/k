from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kast import Atts, KAtt

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Final

    from pyk.kast import AttEntry


PRETTY_TEST_DATA: Final = (
    ('empty', (), ''),
    ('nullary', (Atts.FUNCTION(None),), '[function]'),
    ('two-nullaries', (Atts.FUNCTION(None), Atts.TOTAL(None)), '[function, total]'),
    ('opt-none', (Atts.SYMBOL(None),), '[symbol]'),
    ('opt-some-empty-str', (Atts.SYMBOL(''),), '[symbol("")]'),
    ('opt-some-nonempty-str', (Atts.SYMBOL('foo'),), '[symbol("foo")]'),
    ('multiple', (Atts.SYMBOL('foo'), Atts.FUNCTION(None), Atts.TOTAL(None)), '[symbol("foo"), function, total]'),
)


@pytest.mark.parametrize(
    'test_id, entries,expected',
    PRETTY_TEST_DATA,
    ids=[test_id for test_id, *_ in PRETTY_TEST_DATA],
)
def test_pretty(test_id: str, entries: Iterable[AttEntry], expected: str) -> None:
    # Given
    att = KAtt(entries=entries)

    # When
    actual = att.pretty

    # Then
    assert actual == expected
