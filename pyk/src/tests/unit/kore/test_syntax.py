from __future__ import annotations

from itertools import count
from typing import TYPE_CHECKING

from pyk.kore.prelude import dv
from pyk.kore.syntax import DV, App, String

if TYPE_CHECKING:
    from collections.abc import Callable
    from typing import Final

    from pyk.kore.syntax import Pattern


PATTERN: Final = App(
    'foo',
    (),
    (
        App('bar', (), (dv(0), dv(0))),
        dv(0),
        App('baz', (), (dv(0), dv(0), dv(0))),
    ),
)


def rewriter() -> Callable[[Pattern], Pattern]:
    counter = count()

    def rewrite(pattern: Pattern) -> Pattern:
        match pattern:
            case App():
                return pattern.let(symbol=f'f{next(counter)}')
            case DV():
                return pattern.let(value=String(str(next(counter))))
            case _:
                return pattern

    return rewrite


def test_bottom_up() -> None:
    # Given
    expected = App(
        'f8',
        (),
        (
            App('f2', (), (dv(0), dv(1))),
            dv(3),
            App('f7', (), (dv(4), dv(5), dv(6))),
        ),
    )

    # When
    actual = PATTERN.bottom_up(rewriter())

    # Then
    assert actual == expected


def test_top_down() -> None:
    # Given
    expected = App(
        'f0',
        (),
        (
            App('f1', (), (dv(2), dv(3))),
            dv(4),
            App('f5', (), (dv(6), dv(7), dv(8))),
        ),
    )

    # When
    actual = PATTERN.top_down(rewriter())

    # Then
    assert actual == expected
