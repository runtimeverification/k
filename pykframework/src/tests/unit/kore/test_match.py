from __future__ import annotations

from itertools import count
from typing import TYPE_CHECKING

import pytest

from pykframework.kore.match import (
    app,
    arg,
    args,
    case_symbol,
    inj,
    kore_bytes,
    kore_int,
    kore_list_of,
    kore_map_of,
    kore_set_of,
    kore_str,
)
from pykframework.kore.prelude import dv, list_pattern, map_pattern, set_pattern
from pykframework.kore.syntax import App

if TYPE_CHECKING:
    from collections.abc import Callable
    from typing import Any

    from pykframework.kore.syntax import Pattern


def mk_app(symbol: str) -> Callable[..., App]:
    def res(*args: Pattern) -> App:
        return App(symbol, args=args)

    return res


a, b, c, INJ = (mk_app(symbol) for symbol in ('a', 'b', 'c', 'inj'))


EXTRACT_TEST_DATA = (
    (dv(1), kore_int, 1),
    (dv(b'\f\n\r\t\x00\x80'), kore_bytes, b'\f\n\r\t\x00\x80'),
    (a(), kore_int, None),
    (a(), app(), a()),
    (a(), app('a'), a()),
    (a(), app('b'), None),
    (a(b(), c()), arg(0), b()),
    (a(b(), c()), arg(1), c()),
    (a(b(), c()), arg(2), None),
    (a(b(), c()), arg('b'), b()),
    (a(b(), c()), arg('c'), c()),
    (a(b(), c()), arg('d'), None),
    (a(b(), c()), args(), ()),
    (a(b(), c()), args(0), (b(),)),
    (a(b(), c()), args(0, 1), (b(), c())),
    (a(b(), c()), args(0, 0), (b(), b())),
    (a(b(), c()), args(1, 1), (c(), c())),
    (a(b(), c()), args(0, 1, 1), (b(), c(), c())),
    (a(b(), c()), args(0, 1, 2), None),
    (a(b(), c()), args('b'), (b(),)),
    (a(b(), c()), args('b', 'c'), (b(), c())),
    (a(b(), c()), args('b', 'b'), (b(), b())),
    (a(b(), c()), args('c', 'c'), (c(), c())),
    (a(b(), c()), args('b', 'c', 'c'), (b(), c(), c())),
    (a(b(), c()), args('b', 'c', 'd'), None),
    (INJ(a()), inj, a()),
    (list_pattern(), kore_list_of(kore_int), ()),
    (list_pattern(dv(0), dv(1), dv(2)), kore_list_of(kore_int), (0, 1, 2)),
    (set_pattern(), kore_set_of(kore_int), ()),
    (set_pattern(dv(0), dv(1), dv(2)), kore_set_of(kore_int), (0, 1, 2)),
    (set_pattern(), kore_set_of(kore_int), ()),
    (map_pattern(), kore_map_of(kore_int, kore_str), ()),
    (
        map_pattern((dv(0), dv('a')), (dv(1), dv('b')), (dv(2), dv('c'))),
        kore_map_of(kore_int, kore_str),
        ((0, 'a'), (1, 'b'), (2, 'c')),
    ),
    (map_pattern(cell='ACell'), kore_map_of(kore_int, kore_str, cell='ACell'), ()),
    (
        map_pattern((dv(0), dv('a')), (dv(1), dv('b')), (dv(2), dv('c')), cell='ACell'),
        kore_map_of(kore_int, kore_str, cell='ACell'),
        ((0, 'a'), (1, 'b'), (2, 'c')),
    ),
    (
        a(),
        case_symbol(
            ('a', lambda x: x.symbol),
            ('b', lambda x: x.symbol),
        ),
        'a',
    ),
    (
        b(),
        case_symbol(
            ('a', lambda x: x.symbol),
            ('b', lambda x: x.symbol),
        ),
        'b',
    ),
    (
        c(),
        case_symbol(
            ('a', lambda x: x.symbol),
            ('b', lambda x: x.symbol),
        ),
        None,
    ),
    (
        c(),
        case_symbol(
            ('a', lambda x: x.symbol),
            ('b', lambda x: x.symbol),
            default=lambda x: 'default',
        ),
        'default',
    ),
)


@pytest.mark.parametrize(
    'data,extract,expected',
    EXTRACT_TEST_DATA,
    ids=count(),
)
def test_extract(data: Any, extract: Callable[[Any], Any], expected: Any) -> None:
    if expected is None:
        with pytest.raises(ValueError):
            actual = extract(data)

    else:
        actual = extract(data)
        assert actual == expected
