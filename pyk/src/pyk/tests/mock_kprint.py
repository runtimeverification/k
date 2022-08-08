from ..ktool.kprint import KPrint


class MockKPrint(KPrint):
    def __init__(self):
        self._symbol_table = {}
        return
