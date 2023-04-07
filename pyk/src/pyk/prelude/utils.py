from __future__ import annotations

from typing import TYPE_CHECKING

from .kbool import boolToken
from .kint import intToken
from .string import stringToken

if TYPE_CHECKING:
    pass

    from ..kast.inner import KToken


def token(x: bool | int | str) -> KToken:
    if type(x) is bool:
        return boolToken(x)
    if type(x) is int:
        return intToken(x)
    if type(x) is str:
        return stringToken(x)
    raise AssertionError()
