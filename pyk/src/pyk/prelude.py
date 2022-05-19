from typing import Iterable, Union

from .kast import BOOL, BOTTOM, INT, STRING, TOP, TRUE, KApply, KInner, KToken


def buildAssoc(unit: KInner, join: str, ls: Iterable[KInner]) -> KInner:
    """Build an associative binary operator term given the join and unit ops.

    -   Input: unit, join, and list of elements to join.
    -   Output: cons-list style construction of the joined term.
    """
    ls = list(filter(lambda l: l != unit, ls))
    if len(ls) == 0:
        return unit
    if len(ls) == 1:
        return ls[0]
    if ls[0] == unit:
        return buildAssoc(unit, join, ls[1:])
    return KApply(join, [ls[0], buildAssoc(unit, join, ls[1:])])


def buildCons(unit, cons, ls):
    """Build a cons operator term given the cons and unit ops.

    -   Input: unit, cons, and list of elements to join.
    -   Output: cons-list style construction of the joined term.
    """
    if len(ls) == 0:
        return unit
    return KApply(cons, [ls[0], buildCons(unit, cons, ls[1:])])


def token(x: Union[bool, int, str]) -> KToken:
    if type(x) is bool:
        return boolToken(x)
    if type(x) is int:
        return intToken(x)
    if type(x) is str:
        return stringToken(x)
    assert False


def boolToken(b: bool) -> KToken:
    return KToken('true' if b else 'false', BOOL)


def intToken(i: int) -> KToken:
    return KToken(str(i), INT)


def stringToken(s: str) -> KToken:
    return KToken(f'"{s}"', STRING)


def ltInt(i1, i2):
    return KApply('_<Int_', [i1, i2])


def leInt(i1, i2):
    return KApply('_<=Int_', [i1, i2])


def mlEquals(a1, a2):
    return KApply('#Equals', [a1, a2])


def mlEqualsTrue(b):
    return mlEquals(TRUE, b)


def mlTop():
    return TOP


def mlBottom():
    return BOTTOM


def mlAnd(cs):
    return buildAssoc(mlTop(), '#And', cs)


def mlOr(cs):
    return buildAssoc(mlBottom(), '#Or', cs)


def mlImplies(an, co):
    return KApply('#Implies', [an, co])
