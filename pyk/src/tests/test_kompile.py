from pyk.kompile import _subsort_dict
from pyk.kore.syntax import Attr, Axiom, Definition, Module, Sort, SortApp, SortVar, Top


def test_subsort_dict() -> None:
    def sort_axiom(subsort: Sort, supersort: Sort) -> Axiom:
        r = SortVar('R')
        return Axiom((r,), Top(r), attrs=(Attr('subsort', (subsort, supersort)),))

    a, b, c, d = (SortApp(name) for name in ['a', 'b', 'c', 'd'])

    # When
    definition = Definition(
        (
            Module(
                'MODULE-1',
                (sort_axiom(a, d), sort_axiom(b, d)),
            ),
            Module('MODULE-2', (sort_axiom(b, c),)),
        )
    )
    expected = {
        c: {b},
        d: {a, b},
    }

    # When
    actual = _subsort_dict(definition)

    # Then
    assert actual == expected
