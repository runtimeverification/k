from itertools import count
from typing import Any, Callable

import pytest

from pyk.kore.match import app, arg, args, case_symbol, inj, kore_int, kore_list_of, kore_map_of, kore_set_of, kore_str
from pyk.kore.prelude import dv, kore_list, kore_map, kore_set
from pyk.kore.syntax import App, Pattern


def mk_app(symbol: str) -> Callable[..., App]:
    def res(*args: Pattern) -> App:
        return App(symbol, args=args)

    return res


a, b, c, INJ = (mk_app(symbol) for symbol in ('a', 'b', 'c', 'inj'))


EXTRACT_TEST_DATA = (
    (dv(1), kore_int, 1),
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
    (kore_list(), kore_list_of(kore_int), ()),
    (kore_list(dv(0), dv(1), dv(2)), kore_list_of(kore_int), (0, 1, 2)),
    (kore_set(), kore_set_of(kore_int), ()),
    (kore_set(dv(0), dv(1), dv(2)), kore_set_of(kore_int), (0, 1, 2)),
    (kore_set(), kore_set_of(kore_int), ()),
    (kore_map(), kore_map_of(kore_int, kore_str), ()),
    (
        kore_map((dv(0), dv('a')), (dv(1), dv('b')), (dv(2), dv('c'))),
        kore_map_of(kore_int, kore_str),
        ((0, 'a'), (1, 'b'), (2, 'c')),
    ),
    (kore_map(cell='ACell'), kore_map_of(kore_int, kore_str, cell='ACell'), ()),
    (
        kore_map((dv(0), dv('a')), (dv(1), dv('b')), (dv(2), dv('c')), cell='ACell'),
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
