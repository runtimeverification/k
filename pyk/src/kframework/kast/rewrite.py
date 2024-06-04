from __future__ import annotations

import logging
from typing import TYPE_CHECKING

from .att import WithKAtt
from .inner import KApply, KToken, bottom_up

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Final, TypeVar

    from .inner import KInner, KRewrite

    KI = TypeVar('KI', bound=KInner)
    W = TypeVar('W', bound=WithKAtt)

_LOGGER: Final = logging.getLogger(__name__)


def indexed_rewrite(kast: KInner, rewrites: Iterable[KRewrite]) -> KInner:
    token_rewrites: list[KRewrite] = []
    apply_rewrites: dict[str, list[KRewrite]] = {}
    other_rewrites: list[KRewrite] = []
    for r in rewrites:
        if type(r.lhs) is KToken:
            token_rewrites.append(r)
        elif type(r.lhs) is KApply:
            if r.lhs.label.name in apply_rewrites:
                apply_rewrites[r.lhs.label.name].append(r)
            else:
                apply_rewrites[r.lhs.label.name] = [r]
        else:
            other_rewrites.append(r)

    def _apply_rewrites(_kast: KInner) -> KInner:
        if type(_kast) is KToken:
            for tr in token_rewrites:
                _kast = tr.apply_top(_kast)
        elif type(_kast) is KApply:
            if _kast.label.name in apply_rewrites:
                for ar in apply_rewrites[_kast.label.name]:
                    _kast = ar.apply_top(_kast)
        else:
            for _or in other_rewrites:
                _kast = _or.apply_top(_kast)
        return _kast

    orig_kast: KInner = kast
    new_kast: KInner | None = None
    while orig_kast != new_kast:
        if new_kast is None:
            new_kast = orig_kast
        else:
            orig_kast = new_kast
        new_kast = bottom_up(_apply_rewrites, new_kast)
    return new_kast
