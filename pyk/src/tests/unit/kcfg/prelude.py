from pyk.kast.inner import KApply, KVariable
from pyk.prelude.kint import ltInt, intToken, geInt
from pyk.prelude.ml import mlEqualsTrue


def lt(var: str, n: int) -> KApply:
    return mlEqualsTrue(ltInt(KVariable(var), intToken(n)))


def ge(var: str, n: int) -> KApply:
    return mlEqualsTrue(geInt(KVariable(var), intToken(n)))


def config(var: str) -> KApply:
    return KApply('<top>', KVariable(var))


def config_int(n: int) -> KApply:
    return KApply('<top>', intToken(n))

