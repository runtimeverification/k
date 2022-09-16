from typing import Union

from ..kast import KToken
from .kbool import boolToken
from .kint import intToken
from .string import stringToken


def token(x: Union[bool, int, str]) -> KToken:
    if type(x) is bool:
        return boolToken(x)
    if type(x) is int:
        return intToken(x)
    if type(x) is str:
        return stringToken(x)
    raise AssertionError()
