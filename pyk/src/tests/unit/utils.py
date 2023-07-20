from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING

from pyk.kast.inner import KApply, KLabel, KVariable

if TYPE_CHECKING:
    from typing import Final


TEST_DATA_DIR: Final = (Path(__file__).parent / 'test-data').resolve(strict=True)

a, b, c = map(KApply, ('a', 'b', 'c'))
x, y, z = map(KVariable, ('x', 'y', 'z'))
f, g, h = map(KLabel, ('f', 'g', 'h'))

k = KLabel('<k>')
