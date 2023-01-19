from typing import Final, Union

from .syntax import DV, SortApp, String

BOOL: Final = SortApp('SortBool')
INT: Final = SortApp('SortInt')
BYTES: Final = SortApp('SortBytes')
STRING: Final = SortApp('SortString')


def dv(val: Union[bool, int, str]) -> DV:
    if type(val) is bool:
        return bool_dv(val)
    if type(val) is int:
        return int_dv(val)
    if type(val) is str:
        return string_dv(val)
    raise TypeError(f'Illegal type: {type(val)}')


def bool_dv(val: bool) -> DV:
    return DV(BOOL, String('true' if val else 'false'))


def int_dv(val: int) -> DV:
    return DV(INT, String(str(val)))


def string_dv(val: str) -> DV:
    return DV(STRING, String(val))
