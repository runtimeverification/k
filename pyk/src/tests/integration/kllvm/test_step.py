from __future__ import annotations

from typing import TYPE_CHECKING

from pyk.kllvm.parser import Parser

from .utils import RuntimeTest

if TYPE_CHECKING:
    from types import ModuleType

    from pyk.kllvm.ast import Pattern


class TestStep(RuntimeTest):
    KOMPILE_MAIN_FILE = 'k-files/steps.k'

    def test_steps_1(self, runtime: ModuleType) -> None:
        term = runtime.Term(start_pattern())
        term.step(0)
        assert str(term) == foo_output(0)
        term.step()
        term.step()
        assert str(term) == foo_output(2)
        term.step(200)
        assert str(term) == bar_output()

    def test_steps_2(self, runtime: ModuleType) -> None:
        term = runtime.Term(start_pattern())
        assert str(term) == foo_output(0)
        term.step(50)
        assert str(term) == foo_output(50)
        term.step(-1)
        assert str(term) == bar_output()

    def test_steps_3(self, runtime: ModuleType) -> None:
        term = runtime.Term(start_pattern())
        term.run()
        assert str(term) == bar_output()


def start_pattern() -> Pattern:
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
    return Parser.from_string(text).pattern()


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
