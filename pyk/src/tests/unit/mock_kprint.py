from __future__ import annotations

from functools import cached_property
from typing import TYPE_CHECKING

from pyk.kast.outer import KDefinition, KFlatModule
from pyk.ktool.kprint import KPrint

if TYPE_CHECKING:
    from pyk.ktool.kprint import SymbolTable


class MockKPrint(KPrint):
    def __init__(self) -> None:  # TODO should be unnecessary
        pass

    @cached_property
    def definition(self) -> KDefinition:
        return KDefinition('MOCK', [KFlatModule('MOCK', [])], [])

    @cached_property
    def symbol_table(self) -> SymbolTable:
        return {}
