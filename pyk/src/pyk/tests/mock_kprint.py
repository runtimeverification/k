from ..kast import KDefinition, KFlatModule
from ..ktool.kprint import KPrint


class MockKPrint(KPrint):
    def __init__(self):
        self._definition = KDefinition('MOCK', [KFlatModule('MOCK', [])], [])
        self._symbol_table = {}
        return
