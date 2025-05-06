from __future__ import annotations

from pyk.cterm.show import CTermShow
from pyk.kast.outer import KDefinition, KFlatModule


class MockCTermShow(CTermShow):
    def __init__(self) -> None:
        definition = KDefinition('MOCK', [KFlatModule('MOCK', [])], [])
        super().__init__(definition)
