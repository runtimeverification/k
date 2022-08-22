from pyk.kast import KDefinition, KFlatModule
from pyk.ktool.kprint import KPrint


class MockKPrint(KPrint):
    def __init__(self):
        self._definition = KDefinition('MOCK', [KFlatModule('MOCK', [])], [])
        self._symbol_table = {}
        return
