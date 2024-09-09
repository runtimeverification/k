from pyk.kast.inner import KApply, KVariable
from pyk.prelude.kint import geInt, intToken, ltInt
from pyk.prelude.ml import mlEqualsTrue


def lt_ml(var: str, n: int) -> KApply:
    return mlEqualsTrue(ltInt(KVariable(var), intToken(n)))


def ge_ml(var: str, n: int) -> KApply:
    return mlEqualsTrue(geInt(KVariable(var), intToken(n)))
