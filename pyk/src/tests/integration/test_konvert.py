from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kast.outer import read_kast_definition
from pyk.konvert import module_to_kore
from pyk.kore.parser import KoreParser
from pyk.kore.syntax import SortDecl, Symbol, SymbolDecl

from .utils import K_FILES

if TYPE_CHECKING:
    from collections.abc import Container
    from pathlib import Path
    from typing import Final

    from pyk.kast.outer import KDefinition
    from pyk.kore.syntax import Module, Sentence
    from pyk.testing import Kompiler


@pytest.fixture(scope='module')
def imp_dir(kompile: Kompiler) -> Path:
    return kompile(K_FILES / 'imp.k', backend='haskell')


@pytest.fixture(scope='module')
def imp_kast(imp_dir: Path) -> KDefinition:
    return read_kast_definition(imp_dir / 'compiled.json')


@pytest.fixture(scope='module')
def imp_kore(imp_dir: Path) -> Module:
    kore_text = (imp_dir / 'definition.kore').read_text()
    definition = KoreParser(kore_text).definition()
    return next(module for module in definition if module.name == 'IMP')


IGNORED_SYMBOL_ATTRS: Final = {
    "org'Stop'kframework'Stop'definition'Stop'Production",
    'colors',
    'format',
    'left',
    'priorities',
    'right',
    'strict',
    "symbol'Kywd'",
    'terminals',
}


def test_module_to_kore(imp_kast: KDefinition, imp_kore: Module) -> None:
    # Given
    expected = imp_kore

    # TODO remove
    # Filter out some attributes for now
    expected = discard_symbol_attrs(expected, IGNORED_SYMBOL_ATTRS)

    # When
    actual = module_to_kore(imp_kast)
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
