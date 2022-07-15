from ..ktool.kprint import KPrint


class MockKPrint(KPrint):
    def __init__(self):
        self.symbol_table = {}
        return
