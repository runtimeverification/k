from pyk.kast.outer import KDefinition, KFlatModule
from pyk.ktool.kprint import KPrint


class MockKPrint(KPrint):
    def __init__(self) -> None:  # TODO should be unnecessary
        self._definition = KDefinition('MOCK', [KFlatModule('MOCK', [])], [])
        self._symbol_table = {}
