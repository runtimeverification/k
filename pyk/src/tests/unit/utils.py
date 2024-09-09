from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING

from pyk.kast.inner import KApply, KLabel, KVariable
from pyk.prelude.kint import geInt, intToken, ltInt
from pyk.prelude.ml import mlEqualsTrue

if TYPE_CHECKING:
    from typing import Final


TEST_DATA_DIR: Final = (Path(__file__).parent / 'test-data').resolve(strict=True)

a, b, c = map(KApply, ('a', 'b', 'c'))
x, y, z = map(KVariable, ('x', 'y', 'z'))
f, g, h = map(KLabel, ('f', 'g', 'h'))

k = KLabel('<k>')


def lt_ml(var: str, n: int) -> KApply:
    return mlEqualsTrue(ltInt(KVariable(var), intToken(n)))


def ge_ml(var: str, n: int) -> KApply:
    return mlEqualsTrue(geInt(KVariable(var), intToken(n)))
