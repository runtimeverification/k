from __future__ import annotations

import sys
from itertools import count
from typing import TYPE_CHECKING

import pytest

from pyk.kore.prelude import dv
from pyk.kore.syntax import DV, App, LeftAssoc, RightAssoc, String

if TYPE_CHECKING:
    from collections.abc import Callable
    from typing import Final

    from pyk.kore.syntax import Assoc, Pattern


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


ASSOC_APP: Final = App('Symbol', (), (dv(0), dv(0), dv(0), dv(0)))

ASSOC_CASES: Final = (
    ('LeftAssoc', 'top_down', LeftAssoc(App('Symbol', (), (dv(0), dv(1), dv(2), dv(3))))),
    ('LeftAssoc', 'bottom_up', LeftAssoc(App('Symbol', (), (dv(0), dv(1), dv(2), dv(3))))),
    ('RightAssoc', 'top_down', RightAssoc(App('Symbol', (), (dv(0), dv(1), dv(2), dv(3))))),
    ('RightAssoc', 'bottom_up', RightAssoc(App('Symbol', (), (dv(0), dv(1), dv(2), dv(3))))),
)


@pytest.mark.parametrize(
    'cls,transformer,expected', ASSOC_CASES, ids=[f'{cls} {transformer}' for cls, transformer, *_ in ASSOC_CASES]
)
def test_assoc_transforms(cls: str, transformer: str, expected: Assoc) -> None:
    # Given
    assoc_cls = getattr(sys.modules[__name__], cls)
    assoc = assoc_cls(app=ASSOC_APP)
    transformer_func = getattr(assoc, transformer)

    # When
    actual = transformer_func(rewriter())

    # Then
    assert actual == expected
