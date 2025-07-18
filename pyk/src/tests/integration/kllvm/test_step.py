from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.testing import RuntimeTest

if TYPE_CHECKING:
    from pyk.kllvm.ast import Pattern
    from pyk.kllvm.runtime import Runtime


class TestStep(RuntimeTest):
    KOMPILE_DEFINITION = """
        module STEPS
            imports INT
            syntax Foo ::= foo(Int) | bar()
            rule foo(I) => foo(I -Int 1) requires I >Int 0
            rule foo(_) => bar() [owise]
        endmodule
    """
    KOMPILE_MAIN_MODULE = 'STEPS'
    KOMPILE_ARGS = {'syntax_module': 'STEPS'}

    def test_steps_1(self, runtime: Runtime, start_pattern: Pattern) -> None:
        term = runtime.term(start_pattern)
        term.step(0)
        assert str(term) == foo_output(0)
        term.step()
        term.step()
        assert str(term) == foo_output(2)
        term.step(200)
        assert str(term) == bar_output()

    def test_steps_2(self, runtime: Runtime, start_pattern: Pattern) -> None:
        term = runtime.term(start_pattern)
        assert str(term) == foo_output(0)
        term.step(50)
        assert str(term) == foo_output(50)
        term.step(-1)
        assert str(term) == bar_output()

    def test_steps_3(self, runtime: Runtime, start_pattern: Pattern) -> None:
        term = runtime.term(start_pattern)
        term.run()
        assert str(term) == bar_output()

    def test_steps_to_pattern(self, runtime: Runtime, start_pattern: Pattern) -> None:
        term = runtime.term(start_pattern)
        term.run()
        pattern = term.pattern
        assert str(pattern) == bar_output()


@pytest.fixture
def start_pattern(load_kllvm: None) -> Pattern:
    from pyk.kllvm.parser import parse_pattern

    """
    <k> foo(100) </k>
    """
    text = r"""
        LblinitGeneratedTopCell{}(
            Lbl'Unds'Map'Unds'{}(
                Lbl'Stop'Map{}(),
                Lbl'UndsPipe'-'-GT-Unds'{}(
                    inj{SortKConfigVar{}, SortKItem{}}(\dv{SortKConfigVar{}}("$PGM")),
                    inj{SortFoo{}, SortKItem{}}(
                        inj{SortFoo{}, SortKItem{}}(
                            Lblfoo'LParUndsRParUnds'STEPS'Unds'Foo'Unds'Int{}(\dv{SortInt{}}("100"))
                        )
                    )
                )
            )
        )
    """
    return parse_pattern(text)


def foo_output(n: int) -> str:
    """
    <k> foo(100 - n) </k>
    """
    return fr"""Lbl'-LT-'generatedTop'-GT-'{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}(inj{{SortFoo{{}}, SortKItem{{}}}}(Lblfoo'LParUndsRParUnds'STEPS'Unds'Foo'Unds'Int{{}}(\dv{{SortInt{{}}}}("{100-n}"))),dotk{{}}())),Lbl'-LT-'generatedCounter'-GT-'{{}}(\dv{{SortInt{{}}}}("0")))"""


def bar_output() -> str:
    """
    <k> bar() </k>
    """
    return r"""Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortFoo{}, SortKItem{}}(Lblbar'LParRParUnds'STEPS'Unds'Foo{}()),dotk{}())),Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0")))"""
