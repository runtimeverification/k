from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kast.outer import read_kast_definition
from pyk.konvert import module_to_kore
from pyk.kore.parser import KoreParser
from pyk.kore.syntax import SortDecl

from .utils import K_FILES

if TYPE_CHECKING:
    from pathlib import Path

    from pyk.kast.outer import KDefinition
    from pyk.kore.syntax import Module
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


def test_module_to_kore(imp_kast: KDefinition, imp_kore: Module) -> None:
    # Given
    expected = imp_kore

    # When
    actual = module_to_kore(imp_kast)

    # Then

    # Check module name and attributes
    assert actual.name == expected.name
    assert actual.attrs == expected.attrs

    # Check if sentences under-approximate
    expected_sentences = set(expected.sentences)
    for sent in actual.sentences:
        if sent not in expected_sentences:
            pytest.fail(f'Invalid sentence: {sent.text}')

    # Check if sentences over-approximate
    actual_sentences = set(actual.sentences)
    for sent in expected.sentences:
        # TODO remove, filter for SortDecl for now
        if not isinstance(sent, SortDecl):
            continue
        if sent not in actual_sentences:
            pytest.fail(f'Missing sentence: {sent.text}')
