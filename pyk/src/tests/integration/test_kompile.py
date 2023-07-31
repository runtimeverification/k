from __future__ import annotations

from typing import TYPE_CHECKING

from pyk.ktool.kompile import KompileBackend
from pyk.testing import KompiledTest

from .utils import K_FILES

if TYPE_CHECKING:
    from pyk.ktool.kompile import DefinitionInfo


class TestHaskellKompile(KompiledTest):
    KOMPILE_MAIN_FILE = K_FILES / 'imp.k'
    KOMPILE_BACKEND = 'haskell'

    def test(self, definition_info: DefinitionInfo) -> None:
        assert definition_info.backend == KompileBackend.HASKELL
        assert definition_info.main_module_name == 'IMP'
        assert definition_info.syntax_module_name == 'IMP-SYNTAX'
        assert definition_info.timestamp >= 0


class TestLlvmKompile(KompiledTest):
    KOMPILE_MAIN_FILE = K_FILES / 'imp.k'
    KOMPILE_BACKEND = 'llvm'

    def test(self, definition_info: DefinitionInfo) -> None:
        assert definition_info.backend == KompileBackend.LLVM
        assert definition_info.main_module_name == 'IMP'
        assert definition_info.syntax_module_name == 'IMP-SYNTAX'
        assert definition_info.timestamp >= 0
