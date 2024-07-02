from __future__ import annotations

from functools import cached_property
from typing import TYPE_CHECKING

from pyk.kast.outer import KDefinition, KFlatModule
from pyk.ktool.kprint import KPrint

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable

    from pyk.kast.pretty import SymbolTable


class MockKPrint(KPrint):
    _patch_symbol_table: Callable[[SymbolTable], None] | None
    _extra_unparsing_modules: Iterable[KFlatModule]

    def __init__(self) -> None:  # TODO should be unnecessary
        self._patch_symbol_table = None
        self._extra_unparsing_modules = ()

    @cached_property
    def definition(self) -> KDefinition:
        return KDefinition('MOCK', [KFlatModule('MOCK', [])], [])
