from __future__ import annotations

from itertools import count
from typing import TYPE_CHECKING

import pytest

from pyk.cterm import CTerm
from pyk.kast.inner import KApply, KSequence
from pyk.kcfg.kcfg import KCFG
from pyk.kcfg.store import OptimizedNodeStore, _Cache
from pyk.prelude.utils import token

from ..utils import a, b, c, f

if TYPE_CHECKING:
    from typing import Final

    from pyk.kast import KInner


EQUAL_TEST_DATA: Final[tuple[tuple[KInner, KInner], ...]] = (
    (token(1), token(1)),
    (token('a'), token('a')),
    (a, a),
    (f(a), f(a)),
    (KSequence([a, b]), KSequence([a, b])),
)


@pytest.mark.parametrize('term1,term2', EQUAL_TEST_DATA, ids=count())
def test_use_cached(term1: KInner, term2: KInner) -> None:
    # Given
    cached_values: _Cache[KInner] = _Cache()

    # When
    id1 = cached_values.cache(term1)
    id2 = cached_values.cache(term2)

    # Then
    assert id1 == id2


NOT_EQUAL_TEST_DATA: Final[tuple[tuple[KInner, KInner], ...]] = (
    (token(1), token(2)),
    (token(1), token('1')),
    (a, b),
    (f(a), f(b)),
    (KSequence([a, b]), KSequence([a, c])),
)


@pytest.mark.parametrize('term1,term2', NOT_EQUAL_TEST_DATA, ids=count())
def test_not_use_cached(term1: KInner, term2: KInner) -> None:
    # Given
    cached_values: _Cache[KInner] = _Cache()

    # When
    id1 = cached_values.cache(term1)
    id2 = cached_values.cache(term2)

    # Then
    assert term1 != term2
    assert id1 != id2


OPTIMIZE_TEST_DATA: Final[tuple[KInner, ...]] = (
    token(1),
    token('a'),
    a,
    f(a),
    KSequence([a, token(3)]),
)


def test_optimized_store() -> None:
    store = OptimizedNodeStore()

    for idx, item in zip(range(0, len(OPTIMIZE_TEST_DATA)), OPTIMIZE_TEST_DATA, strict=True):
        store[idx] = KCFG.Node(idx, CTerm(KApply('<cell>', item), ()))

    for idx, item in zip(range(0, len(OPTIMIZE_TEST_DATA)), OPTIMIZE_TEST_DATA, strict=True):
        assert KCFG.Node(idx, CTerm(KApply('<cell>', item), ())) == store[idx]
