from functools import cached_property

from pyk.kast.outer import KDefinition, KFlatModule
from pyk.ktool.kprint import KPrint, SymbolTable


class MockKPrint(KPrint):
    def __init__(self) -> None:  # TODO should be unnecessary
        pass

    @cached_property
    def definition(self) -> KDefinition:
        return KDefinition('MOCK', [KFlatModule('MOCK', [])], [])

    @cached_property
    def symbol_table(self) -> SymbolTable:
        return {}
