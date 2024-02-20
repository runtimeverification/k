from __future__ import annotations

from typing import TYPE_CHECKING

from pyk.kast import Atts
from pyk.kast.inner import KApply, KAs, KRewrite, KSort
from pyk.kast.outer import KRegexTerminal, KSortSynonym, read_kast_definition
from pyk.utils import single

from .utils import K_FILES

if TYPE_CHECKING:
    from pyk.testing import Kompiler


def test_sort_synonym(kompile: Kompiler) -> None:
    # Given
    definition_dir = kompile(K_FILES / 'sort-synonym.k')
    definition = read_kast_definition(definition_dir / 'compiled.json')
    module = definition.module('SORT-SYNONYM-SYNTAX')

    # When
    sort_synonym = single(sentence for sentence in module if type(sentence) is KSortSynonym)

    # Then
    assert sort_synonym.new_sort == KSort('NewInt')
    assert sort_synonym.old_sort == KSort('Int')


def test_kas(kompile: Kompiler) -> None:
    # Given
    definition_dir = kompile(K_FILES / 'contextual-function.k')
    definition = read_kast_definition(definition_dir / 'compiled.json')
    module = definition.module('CONTEXTUAL-FUNCTION')

    # When
    rule = single(rule for rule in module.rules if rule.att.get(Atts.LABEL) == 'def-get-ctx')

    # Then
    rewrite = rule.body
    assert type(rewrite) is KRewrite
    lhs = rewrite.lhs
    assert type(lhs) is KApply
    kas = lhs.args[0]
    assert isinstance(kas, KAs)


def test_regex_terminal(kompile: Kompiler) -> None:
    # Given
    definition_dir = kompile(K_FILES / 'regex-terminal.k')
    definition = read_kast_definition(definition_dir / 'compiled.json')
    module = definition.module('REGEX-TERMINAL-SYNTAX')
    expected = [
        KRegexTerminal('b', '#', '#'),
        KRegexTerminal('b', 'a', '#'),
        KRegexTerminal('b', '#', 'c'),
        KRegexTerminal('b', 'a', 'c'),
    ]

    # When
    productions = sorted(
        (
            prod
            for prod in module.productions
            if prod.sort.name in {'T0', 'T1', 'T2', 'T3'} and type(prod.items[0]) is KRegexTerminal
        ),
        key=lambda prod: prod.sort.name,
    )
    actual = [prod.items[0] for prod in productions]

    # Then
    assert actual == expected
