from typing import cast

from ..kast import KAst
from ..ktool.kprint import KPrint, prettyPrintKast


class MockKPrint:
    def pretty_print(self, term: KAst) -> str:
        return prettyPrintKast(term, symbol_table={})


def mock_kprint() -> KPrint:
    return cast(KPrint, MockKPrint())
