from __future__ import annotations

from collections import Counter
from typing import TYPE_CHECKING

import pytest

from pyk.kore.parser import KoreParser
from pyk.kore.rule import Rule
from pyk.kore.syntax import App, String

from ..utils import K_FILES

if TYPE_CHECKING:
    from pyk.kore.syntax import Axiom, Definition
    from pyk.testing import Kompiler


@pytest.fixture(scope='module')
def definition(kompile: Kompiler) -> Definition:
    main_file = K_FILES / 'imp.k'
    definition_dir = kompile(main_file=main_file, backend='haskell')
    kore_file = definition_dir / 'definition.kore'
    kore_text = kore_file.read_text()
    definition = KoreParser(kore_text).definition()
    return definition


def test_extract_all(definition: Definition) -> None:
    # When
    rules = Rule.extract_all(definition)

    # Then
    cnt = Counter(type(rule).__name__ for rule in rules)
    assert cnt['RewriteRule']
    assert cnt['FunctionRule']
    assert cnt['AppRule']
    assert cnt['CeilRule']
    assert cnt['EqualsRule']


def test_to_axiom(definition: Definition) -> None:
    def adjust_atts(axiom: Axiom) -> Axiom:
        match axiom.attrs_by_key.get('simplification'):
            case None:
                return axiom.let(attrs=())
            case App(args=(String('' | '50'),)):
                return axiom.let(attrs=(App('simplification'),))
            case attr:
                return axiom.let(attrs=(attr,))

    for axiom in definition.axioms:
        if not Rule.is_rule(axiom):
            continue

        # Given
        expected = adjust_atts(axiom)

        # When
        rule = Rule.from_axiom(axiom)
        actual = rule.to_axiom()

        # Then
        assert expected == actual
