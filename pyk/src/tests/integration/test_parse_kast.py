from __future__ import annotations

from typing import TYPE_CHECKING

from pyk.kast import EMPTY_ATT, Atts
from pyk.kast.inner import KApply, KAs, KRewrite, KSort
from pyk.kast.outer import KRegexTerminal, KSortSynonym, read_kast_definition

if TYPE_CHECKING:
    from pyk.testing import Kompiler


def test_sort_synonym(kompile: Kompiler) -> None:
    # Given
    k_text = """
        module SORT-SYNONYM
            imports INT-SYNTAX
            syntax NewInt = Int
        endmodule
    """
    main_module = 'SORT-SYNONYM'
    definition_dir = kompile(definition=k_text, main_module=main_module, syntax_module=main_module)
    definition = read_kast_definition(definition_dir / 'compiled.json')
    module = definition.module(main_module)
    expected = KSortSynonym(new_sort=KSort('NewInt'), old_sort=KSort('Int'))

    # When
    (syntax_synonym,) = (sentence for sentence in module if type(sentence) is KSortSynonym)
    actual = syntax_synonym.let(att=EMPTY_ATT)

    # Then
    assert actual == expected


def test_kas(kompile: Kompiler) -> None:
    # Given
    k_text = """
        module CONTEXTUAL-FUNCTION
            imports INT-SYNTAX

            syntax Int ::= getCtx() [function, total]

            configuration <k> $PGM:KItem </k>
                          <ctx> 0 </ctx>

            rule [[ getCtx() => N ]] <ctx> N </ctx> [label(def-get-ctx)]
        endmodule
    """
    main_module = 'CONTEXTUAL-FUNCTION'
    definition_dir = kompile(definition=k_text, main_module=main_module, syntax_module=main_module)
    definition = read_kast_definition(definition_dir / 'compiled.json')
    module = definition.module(main_module)

    # When
    (rule,) = (rule for rule in module.rules if rule.att.get(Atts.LABEL) == 'def-get-ctx')

    # Then
    rewrite = rule.body
    assert type(rewrite) is KRewrite
    lhs = rewrite.lhs
    assert type(lhs) is KApply
    kas = lhs.args[0]
    assert isinstance(kas, KAs)


def test_regex_terminal(kompile: Kompiler) -> None:
    # Given
    k_text = """
        module REGEX-TERMINAL
            syntax T0 ::= r"b"            [token]
            syntax T1 ::= r"(?<!a)b"      [token]
            syntax T2 ::= r"b(?!c)"       [token]
            syntax T3 ::= r"(?<!a)b(?!c)" [token]
        endmodule
    """
    main_module = 'REGEX-TERMINAL'
    definition_dir = kompile(definition=k_text, main_module=main_module, syntax_module=main_module)
    definition = read_kast_definition(definition_dir / 'compiled.json')
    module = definition.module(main_module)
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
