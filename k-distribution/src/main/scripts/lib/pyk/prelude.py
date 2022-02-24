from .kast import KApply, KConstant, KToken


def buildAssoc(unit, join, ls):
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


def boolToken(b):
    return KToken(str(b).lower(), 'Bool')


def intToken(i):
    return KToken(str(i), 'Int')


def stringToken(s):
    return KToken('"' + s + '"', 'String')


def ltInt(i1, i2):
    return KApply('_<Int_', [i1, i2])


def leInt(i1, i2):
    return KApply('_<=Int_', [i1, i2])


def mlEquals(a1, a2):
    return KApply('#Equals', [a1, a2])


def mlEqualsTrue(b):
    return mlEquals(boolToken(True), b)


def mlTop():
    return KConstant('#Top')


def mlBottom():
    return KConstant('#Bottom')


def mlAnd(cs):
    return buildAssoc(mlTop(), '#And', cs)


def mlOr(cs):
    return buildAssoc(mlBottom(), '#Or', cs)


def mlImplies(an, co):
    return KApply('#Implies', [an, co])
