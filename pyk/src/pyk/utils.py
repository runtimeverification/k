from __future__ import annotations

import hashlib
import string
from typing import TYPE_CHECKING, Generic, Mapping, TypeVar, cast, overload

from .dequote import dequoted, enquoted

if TYPE_CHECKING:
    from typing import Any, Callable, Dict, Final, Hashable, Iterable, Iterator, List, Optional, Tuple, Type

    P1 = TypeVar('P1')
    P2 = TypeVar('P2')
    P3 = TypeVar('P3')
    P4 = TypeVar('P4')
    Q = TypeVar('Q')
    R1 = TypeVar('R1')
    R2 = TypeVar('R2')
    R3 = TypeVar('R3')
    R4 = TypeVar('R4')
    T = TypeVar('T')
    S = TypeVar('S')
    H = TypeVar('H', bound=Hashable)

P = TypeVar('P')
R = TypeVar('R')
K = TypeVar('K')
V = TypeVar('V')


# Based on: https://stackoverflow.com/a/2704866
# Perhaps one day: https://peps.python.org/pep-0603/
class FrozenDict(Mapping[K, V]):
    _dict: Dict[K, V]
    _hash: Optional[int]

    # TODO overload
    # TODO try __init__(self: FrozenDict[str, V], **kwargs: V)
    def __init__(self, *args: Any, **kwargs: Any):
        self._dict = dict(*args, **kwargs)
        self._hash = None

    def __iter__(self) -> Iterator[K]:
        return iter(self._dict)

    def __len__(self) -> int:
        return len(self._dict)

    def __getitem__(self, key: K) -> V:
        return self._dict[key]

    def __hash__(self) -> int:
        if self._hash is None:
            h = 0
            for pair in self.items():
                h ^= hash(pair)
            self._hash = h
        return self._hash

    def __str__(self) -> str:
        return f'FrozenDict({str(self._dict)})'

    def __repr__(self) -> str:
        return f'FrozenDict({repr(self._dict)})'


EMPTY_FROZEN_DICT: Final[FrozenDict] = FrozenDict()


def check_type(x: Any, typ: Type[T]) -> T:
    if not isinstance(x, typ):
        raise ValueError(f'Expected object of type {typ.__name__}, got: {x}')
    return x


def raised(f: Callable, *args: Any, **kwargs: Any) -> Optional[BaseException]:
    try:
        f(*args, **kwargs)
    except BaseException as e:
        return e

    return None


def merge_with(f: Callable[[V, V], V], d1: Mapping[K, V], d2: Mapping[K, V]) -> Dict[K, V]:
    res = dict(d1)
    for k, v2 in d2.items():
        if k in d1:
            v1 = d1[k]
            res[k] = f(v1, v2)
        else:
            res[k] = v2
    return res


def filter_none(mapping: Mapping[K, V]) -> Dict[K, V]:
    return {k: v for k, v in mapping.items() if v is not None}


# Higher-order functions


class Chainable(Generic[P, R]):
    _f: Callable[[P], R]

    def __init__(self, f: Callable[[P], R]):
        self._f = f

    def __call__(self, p: P) -> R:
        return self._f(p)

    def __rshift__(self, other: Callable[[R], Q]) -> Chainable[P, Q]:
        return Chainable(lambda p: other(self(p)))


chain: Final[Chainable[Any, Any]] = Chainable(lambda x: x)


def none(x: Any) -> None:
    pass


def maybe(f: Callable[[P], R]) -> Callable[[Optional[P]], Optional[R]]:
    def res(p: Optional[P]) -> Optional[R]:
        return f(p) if p is not None else None

    return res


@overload
def tuple_of() -> Callable[[Tuple[()]], Tuple[()]]:
    ...


@overload
def tuple_of(
    f1: Callable[[P1], R1],
    /,
) -> Callable[[Tuple[P1]], Tuple[R1]]:
    ...


@overload
def tuple_of(
    f1: Callable[[P1], R1],
    f2: Callable[[P2], R2],
    /,
) -> Callable[[Tuple[P1, P2]], Tuple[R1, R2]]:
    ...


@overload
def tuple_of(
    f1: Callable[[P1], R1],
    f2: Callable[[P2], R2],
    f3: Callable[[P3], R3],
    /,
) -> Callable[[Tuple[P1, P2, P3]], Tuple[R1, R2, R3]]:
    ...


@overload
def tuple_of(
    f1: Callable[[P1], R1],
    f2: Callable[[P2], R2],
    f3: Callable[[P3], R3],
    f4: Callable[[P4], R4],
    /,
) -> Callable[[Tuple[P1, P2, P3, P4]], Tuple[R1, R2, R3, R4]]:
    ...


def tuple_of(*args: Callable) -> Callable:
    def res(t: Tuple) -> Tuple:
        return tuple(f(x) for f, x in zip(args, t))

    return res


def case(
    cases: Iterable[Tuple[Callable[[P], bool], Callable[[P], R]]],
    default: Optional[Callable[[P], R]] = None,
) -> Callable[[P], R]:
    def res(p: P) -> R:
        for cond, then in cases:  # noqa: B905
            if cond(p):
                return then(p)

        if default is not None:
            return default(p)

        raise ValueError(f'No match found for: {p}')

    return res


# Iterables


def find_common_items(l1: Iterable[T], l2: Iterable[T]) -> Tuple[List[T], List[T], List[T]]:
    common = []
    for i in l1:
        if i in l2:
            common.append(i)
    new_l1 = []
    new_l2 = []
    for i in l1:
        if i not in common:
            new_l1.append(i)
    for i in l2:
        if i not in common:
            new_l2.append(i)
    return (common, new_l1, new_l2)


def intersperse(iterable: Iterable[T], delimiter: T) -> Iterator[T]:
    it = iter(iterable)

    try:
        yield next(it)
    except StopIteration:
        return

    for x in it:
        yield delimiter
        yield x


def unique(iterable: Iterable[H]) -> Iterator[H]:
    elems = set()
    for elem in iterable:
        if elem in elems:
            continue
        else:
            elems.add(elem)
            yield elem


def single(iterable: Iterable[T]) -> T:
    it = iter(iterable)
    sentinel = object()

    fst = next(it, sentinel)
    if fst is sentinel:
        raise ValueError('Expected a single element, found none')
    fst = cast('T', fst)

    snd = next(it, sentinel)
    if snd is not sentinel:
        raise ValueError('Expected a single element, found more', fst, snd)

    return fst


def some(iterable: Iterable[T]) -> Optional[T]:
    return next(iter(iterable), None)


def repeat_last(iterable: Iterable[T]) -> Iterator[T]:
    it = iter(iterable)
    last: Optional[T] = None
    while True:
        try:
            last = next(it)
            yield last

        except StopIteration:
            if last is None:
                return

            yield last


def nonempty_str(x: Any) -> str:
    if x is None:
        raise ValueError('Expected nonempty string, found: null.')
    if type(x) is not str:
        raise TypeError('Expected nonempty string, found: {type(x)}')
    if x == '':
        raise ValueError("Expected nonempty string, found: ''")
    return x


def add_indent(indent: str, lines: Iterable[str]) -> List[str]:
    return [indent + line for line in lines]


def is_hexstring(x: str) -> bool:
    return all(c in string.hexdigits for c in x)


# Hashes


def hash_str(x: Any) -> str:
    hash = hashlib.sha256()
    hash.update(str(x).encode('utf-8'))
    return str(hash.hexdigest())


def is_hash(x: Any) -> bool:
    # NB! currently only sha256 in hexdec form is detected
    # 2b9e b7c5 441e 9f7e 97f9 a4e5 fc04 a0f7 9f62 c8e9 605a ad1e 02db e8de 3c21 0422
    # 1    2    3    4    5    6    7    8    9    10   11   12   13   14   15   16
    return type(x) is str and len(x) == 64 and is_hexstring(x)


def shorten_hash(h: str, left_chars: int = 6, right_chars: int = 6) -> str:
    left = h[0:left_chars] if left_chars > 0 else ''
    right = h[-right_chars:] if right_chars > 0 else ''
    return left + '..' + right


def shorten_hashes(value: Any, left_chars: int = 6, right_chars: int = 6) -> Any:
    result: Any = None
    if is_hash(value):
        result = shorten_hash(value, left_chars, right_chars)
    elif type(value) is tuple:
        result = tuple([shorten_hashes(item) for item in value])
    elif type(value) is list:
        result = [shorten_hashes(v) for v in value]
    elif type(value) is dict:
        result = {}
        for k, v in value.items():
            result[shorten_hashes(k)] = shorten_hashes(v)
    elif type(value) is set:
        result = set()
        for item in value:
            result.add(shorten_hashes(item))
    else:
        result = value
    return result


def deconstruct_short_hash(h: str) -> Tuple[str, str]:
    x = h.lower()
    if is_hash(x):
        return (x, x)
    (l, sep, r) = x.partition('..')
    if sep == '..' and is_hexstring(l) and is_hexstring(r):
        return (l, r)
    raise ValueError(f'Bad short hash: {h}')


def compare_short_hashes(lhs: str, rhs: str) -> bool:
    (l0, l1) = deconstruct_short_hash(lhs)
    (r0, r1) = deconstruct_short_hash(rhs)
    return (l0.startswith(r0) or r0.startswith(l0)) and (l1.endswith(r1) or r1.endswith(l1))


def enquote_str(s: str) -> str:
    return ''.join(enquoted(s))


def dequote_str(s: str) -> str:
    return ''.join(dequoted(s))
