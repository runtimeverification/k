from __future__ import annotations

from pyk.kore.kompiled import KoreSortTable
from pyk.kore.parser import KoreParser
from pyk.kore.syntax import SortApp


def test_kore_sort_table() -> None:
    # When
    definition_text = r"""
        []
        module MODULE-1
            axiom{R} \top{R}() [subsort{A{}, B{}}()]
            axiom{R} \top{R}() [subsort{B{}, C{}}()]
        endmodule []
        module MODULE-2
            axiom{R} \top{R}() [subsort{B{}, D{}}()]
        endmodule []
    """
    definition = KoreParser(definition_text).definition()
    sort_table = KoreSortTable.for_definition(definition)

    a, b, c, d = (SortApp(name) for name in ['A', 'B', 'C', 'D'])
    expected = {
        b: {a},
        c: {a, b},
        d: {a, b},
    }

    # When
    actual = sort_table._subsort_table

    # Then
    assert actual == expected
