from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kast.outer import read_kast_definition
from pyk.konvert import module_to_kore
from pyk.kore.parser import KoreParser
from pyk.kore.rule import Rule
from pyk.kore.syntax import Axiom, SortDecl, SortVar, Symbol, SymbolDecl
from pyk.ktool.kompile import DefinitionInfo

from ..utils import TEST_DATA_DIR

if TYPE_CHECKING:
    from collections.abc import Container
    from pathlib import Path
    from typing import Any, Final

    from pytest import FixtureRequest

    from pyk.kast.outer import KDefinition
    from pyk.kore.syntax import Module, Sentence
    from pyk.testing import Kompiler


MODULE_TO_KORE_DIR: Final = TEST_DATA_DIR / 'module-to-kore'

# Extra kompile kwargs for files that need non-default options.
EXTRA_KOMPILE_ARGS: Final[dict[str, dict[str, Any]]] = {
    'coverage.k': {'coverage': True},
}

DEFINITION_FILES: Final = tuple(MODULE_TO_KORE_DIR.glob('*.k'))


@pytest.fixture(
    params=DEFINITION_FILES,
    ids=[file.name for file in DEFINITION_FILES],
)
def definition_dir(request: FixtureRequest, kompile: Kompiler) -> Path:
    path: Path = request.param
    extra = EXTRA_KOMPILE_ARGS.get(path.name, {})
    return kompile(main_file=path, **extra)


@pytest.fixture
def definition_info(definition_dir: Path) -> DefinitionInfo:
    return DefinitionInfo(definition_dir)


@pytest.fixture
def kast_defn(definition_dir: Path) -> KDefinition:
    return read_kast_definition(definition_dir / 'compiled.json')


@pytest.fixture
def kore_module(definition_dir: Path, definition_info: DefinitionInfo) -> Module:
    kore_text = (definition_dir / 'definition.kore').read_text()
    definition = KoreParser(kore_text).definition()
    return next(module for module in definition if module.name == definition_info.main_module_name)


IGNORED_SYMBOL_ATTRS: Final = {"symbol'Kywd'"}


def test_module_to_kore(kast_defn: KDefinition, kore_module: Module) -> None:
    # Given
    expected = kore_module

    # TODO remove
    # Filter out some attributes for now
    expected = discard_symbol_attrs(expected, IGNORED_SYMBOL_ATTRS)

    # When
    actual = module_to_kore(kast_defn)
    actual = discard_symbol_attrs(actual, IGNORED_SYMBOL_ATTRS)

    # Normalize sort-declaration variable names to canonical SortS{i} form on both
    # sides before comparing.  pyk preserves the original K source names (e.g.
    # SortWidth for MInt{Width}), while the Java backend emits SortS0, SortS1, …;
    # the names are locally bound in declarations so only arity matters.
    expected = canonicalize_sort_decl_vars(expected)
    actual = canonicalize_sort_decl_vars(actual)

    # Then

    # Check module name and attributes
    assert expected.name == actual.name
    assert expected.attrs == actual.attrs

    check_generated_sentences(actual, expected)
    check_missing_sentences(actual, expected)


def discard_symbol_attrs(module: Module, attrs: Container[str]) -> Module:
    def update(sentence: Sentence) -> Sentence:
        if not isinstance(sentence, SymbolDecl):
            return sentence
        return sentence.let(attrs=tuple(attr for attr in sentence.attrs if attr.symbol not in attrs))

    return module.let(sentences=tuple(update(sentence) for sentence in module.sentences))


def canonicalize_sort_decl_vars(module: Module) -> Module:
    # Sort-declaration variable names are locally bound; replace them with
    # canonical SortS{i} names so that pyk's preserved source names (e.g.
    # SortWidth) compare equal to Java's generated names (SortS0).
    def update(sentence: Sentence) -> Sentence:
        if not isinstance(sentence, SortDecl):
            return sentence
        canonical = tuple(SortVar(f'SortS{i}') for i in range(len(sentence.vars)))
        return sentence.let(vars=canonical)

    return module.let(sentences=tuple(update(sentence) for sentence in module.sentences))


def check_generated_sentences(actual: Module, expected: Module) -> None:
    def find_expected_sentence(sentence: Sentence, expected: Module) -> Sentence | None:
        match sentence:
            case SortDecl(name=name):
                return next(
                    (
                        sentence
                        for sentence in expected.sentences
                        if isinstance(sentence, SortDecl) and sentence.name == name
                    ),
                    None,
                )
            case SymbolDecl(symbol=Symbol(name=name)):
                return next(
                    (
                        sentence
                        for sentence in expected.sentences
                        if isinstance(sentence, SymbolDecl) and sentence.symbol.name == name
                    ),
                    None,
                )
            case _:
                return None  # TODO refine further here

    expected_sentences = set(expected.sentences)
    for sent in actual.sentences:
        if sent in expected_sentences:
            continue

        expected_sent = find_expected_sentence(sent, expected)
        if expected_sent is None:
            pytest.fail(f'Invalid sentence: {sent.text}')

        # Fail with diff
        assert expected_sent.text == sent.text


def check_missing_sentences(actual: Module, expected: Module) -> None:
    actual_sentences = set(actual.sentences)
    for sent in expected.sentences:
        # TODO remove
        # Do not check rule axioms for now
        if isinstance(sent, Axiom) and Rule.is_rule(sent):
            continue
        if sent not in actual_sentences:
            pytest.fail(f'Missing sentence: {sent.text}')
