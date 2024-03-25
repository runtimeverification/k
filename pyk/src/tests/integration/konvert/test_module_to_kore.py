from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kast.outer import read_kast_definition
from pyk.konvert import module_to_kore
from pyk.kore.parser import KoreParser
from pyk.kore.syntax import SortDecl, Symbol, SymbolDecl
from pyk.ktool.kompile import DefinitionInfo

from ..utils import TEST_DATA_DIR

if TYPE_CHECKING:
    from collections.abc import Container
    from pathlib import Path
    from typing import Final

    from pytest import FixtureRequest

    from pyk.kast.outer import KDefinition
    from pyk.kore.syntax import Module, Sentence
    from pyk.testing import Kompiler


DEFINITION_FILES: Final = tuple((TEST_DATA_DIR / 'module-to-kore').glob('*.k'))


@pytest.fixture(
    params=DEFINITION_FILES,
    ids=[file.name for file in DEFINITION_FILES],
)
def definition_dir(request: FixtureRequest, kompile: Kompiler) -> Path:
    return kompile(request.param)


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

    # Then

    # Check module name and attributes
    assert actual.name == expected.name
    assert actual.attrs == expected.attrs

    check_generated_sentences(actual, expected)
    check_missing_sentences(actual, expected)


def discard_symbol_attrs(module: Module, attrs: Container[str]) -> Module:
    def update(sentence: Sentence) -> Sentence:
        if not isinstance(sentence, SymbolDecl):
            return sentence
        return sentence.let(attrs=tuple(attr for attr in sentence.attrs if attr.symbol not in attrs))

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
        assert sent.text == expected_sent.text


def check_missing_sentences(actual: Module, expected: Module) -> None:
    actual_sentences = set(actual.sentences)
    for sent in expected.sentences:
        # TODO remove
        # Filter for SortDecl and SymbolDecl for now
        if not isinstance(sent, SortDecl):
            continue
        if sent not in actual_sentences:
            pytest.fail(f'Missing sentence: {sent.text}')
