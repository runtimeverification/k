from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kast import KAtt
from pyk.ktool.kompile import KompileBackend, KompileNotFoundError, kompile
from pyk.testing import KompiledTest

from .utils import K_FILES

if TYPE_CHECKING:
    from pyk.kast.inner import KLabel
    from pyk.kast.outer import KDefinition
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


def test_kompile_not_found(monkeypatch: pytest.MonkeyPatch) -> None:
    k_file = K_FILES / 'imp-verification.k'
    bad_kompile = 'bad-name-of-kompile'
    monkeypatch.setenv('PATH', '')

    with pytest.raises(KompileNotFoundError):
        kompile(k_file, command=[bad_kompile])


class TestKLabel(KompiledTest):
    KOMPILE_MAIN_FILE = K_FILES / 'klabel.k'

    def test(self, definition: KDefinition) -> None:
        # Given
        module = definition.module('KLABEL')

        def klabel_defined_at_line(line: int) -> KLabel:
            (prod,) = (prod for prod in module.productions if prod.att.get(KAtt.LOCATION, [None])[0] == line)
            res = prod.klabel
            assert res is not None
            return res

        foo = klabel_defined_at_line(2)
        bar = klabel_defined_at_line(3)
        baz = klabel_defined_at_line(4)
        qux = klabel_defined_at_line(5)

        # Then
        assert foo.name == 'foo'
        assert bar.name == 'bar'
        assert baz.name == 'baz_KLABEL_Foo'
        assert qux.name == 'qux_KLABEL_Foo'
