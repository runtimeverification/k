from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kast import Atts
from pyk.kast.inner import KSort
from pyk.kore.syntax import SortApp
from pyk.ktool.kompile import KompileBackend, KompileNotFoundError, kompile
from pyk.testing import KompiledTest

from .utils import K_FILES

if TYPE_CHECKING:
    from pyk.kast.inner import KLabel
    from pyk.kast.outer import KDefinition
    from pyk.kore.kompiled import KompiledKore
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
    KOMPILE_DEFINITION = """
        module KLABEL
            syntax Foo ::= "foo" [symbol(foo)]
                         | "bar" [klabel(bar), symbol]
                         | "baz" [klabel(baz)]
                         | "qux"
        endmodule
    """
    KOMPILE_MAIN_MODULE = 'KLABEL'
    KOMPILE_ARGS = {'syntax_module': 'KLABEL'}

    def test(self, definition: KDefinition) -> None:
        # Given
        module = definition.module('KLABEL')

        def klabel_defined_at_line(line: int) -> KLabel:
            (prod,) = (prod for prod in module.productions if prod.att.get(Atts.LOCATION, [None])[0] == line)
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


class TestSubsortSymbol(KompiledTest):
    KOMPILE_DEFINITION = """
        module SUBSORT-SYMBOL
            syntax Foo ::= Bar [symbol(bar)]
            syntax Bar
        endmodule
    """
    KOMPILE_MAIN_MODULE = 'SUBSORT-SYMBOL'
    KOMPILE_ARGS = {'syntax_module': 'SUBSORT-SYMBOL'}

    def test(self, definition: KDefinition, kompiled_kore: KompiledKore) -> None:
        # Given
        Foo, Bar = (KSort(name) for name in ['Foo', 'Bar'])  # noqa: N806

        # Then
        assert 'bar' in definition.symbols
        assert Bar not in definition.subsorts(Foo)

        # And given
        SortFoo, SortBar = (SortApp(name) for name in ['SortFoo', 'SortBar'])  # noqa: N806

        # Then
        assert kompiled_kore.symbol_table.resolve('Lblbar') == (SortFoo, (SortBar,))
        assert not kompiled_kore.sort_table.is_subsort(SortBar, SortFoo)
