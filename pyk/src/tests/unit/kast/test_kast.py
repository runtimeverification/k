from __future__ import annotations

from itertools import count
from typing import TYPE_CHECKING

import pytest

from pyk.kast import KInner
from pyk.kast.att import Format
from pyk.kast.inner import KApply, KLabel, KSequence, KSort, KVariable, build_assoc
from pyk.kast.outer import KDefinition, KFlatModule, KImport, KNonTerminal, KProduction, KRegexTerminal, KTerminal
from pyk.prelude.kbool import BOOL
from pyk.prelude.kint import INT
from pyk.prelude.string import STRING
from pyk.prelude.utils import token

from ..utils import f, x, y, z

if TYPE_CHECKING:
    from typing import Any, Final


KVARIABLE_TEST_DATA: Final = (
    ('no-sort', KVariable('Foo'), {'node': 'KVariable', 'name': 'Foo'}),
    (
        'sort',
        KVariable('Foo', sort=KSort('Int')),
        {
            'node': 'KVariable',
            'name': 'Foo',
            'sort': {'node': 'KSort', 'name': 'Int'},
        },
    ),
)


@pytest.mark.parametrize(
    'test_id,var,dct',
    KVARIABLE_TEST_DATA,
    ids=[test_id for test_id, *_ in KVARIABLE_TEST_DATA],
)
def test_kvariable_to_dict(test_id: str, var: KVariable, dct: dict[str, Any]) -> None:
    # When
    actual_var = KInner.from_dict(dct)
    actual_dct = var.to_dict()

    # Then
    assert actual_var == var
    assert actual_dct == dct


KVARIABLE_LET_TEST_DATA: Final = (
    ('let-changes-sort', KVariable('Foo', sort=STRING).let(sort=INT), KVariable('Foo', sort=INT)),
    (
        'let-can-set-sort',
        KVariable('Foo').let(sort=STRING),
        KVariable('Foo', sort=STRING),
    ),
)


@pytest.mark.parametrize(
    'test_id,var,expected',
    KVARIABLE_LET_TEST_DATA,
    ids=[test_id for test_id, *_ in KVARIABLE_LET_TEST_DATA],
)
def test_kvariable_let(test_id: str, var: KVariable, expected: KVariable) -> None:
    # When
    actual = KVariable.from_dict(var.to_dict())

    # Then
    assert actual == expected


KLABEL_TEST_DATA: Final[tuple[list[KSort], ...]] = (
    [],
    [BOOL],
    [BOOL, INT],
    [BOOL, INT, STRING],
)


@pytest.mark.parametrize('params', KLABEL_TEST_DATA, ids=count())
def test_klabel_init(params: list[KSort]) -> None:
    # When
    terms = (
        KLabel('f', params),
        KLabel('f', *params),
        KLabel('f', params=params),
        KLabel(name='f', params=params),
    )

    # Then
    for term in terms:
        assert term.name == 'f'
        assert term.params == tuple(params)


@pytest.mark.parametrize('params', KLABEL_TEST_DATA[1:], ids=count())
def test_klabel_init_multiple_values(params: list[KSort]) -> None:
    # Given
    expected_message = 'KLabel() got multiple values for argument: params'

    with pytest.raises(TypeError) as excinfo:
        # When
        KLabel('f', *params, params=params)  # type: ignore

    actual_message = str(excinfo.value)

    # Then
    assert actual_message == expected_message


@pytest.mark.parametrize('params', KLABEL_TEST_DATA, ids=count())
def test_klabel_init_unkown_keyword(params: list[KSort]) -> None:
    # Given
    expected_message = 'KLabel() got an unexpected keyword argument: key'

    with pytest.raises(TypeError) as excinfo:
        # When
        KLabel('f', *params, key='value')  # type: ignore

    actual_message = str(excinfo.value)

    # Then
    assert actual_message == expected_message


KAPPLY_TEST_DATA: Final[tuple[list[KInner], ...]] = (
    [],
    [x],
    [x, y],
    [x, y, z],
)


@pytest.mark.parametrize('args', KAPPLY_TEST_DATA, ids=count())
def test_kapply_init(args: list[KInner]) -> None:
    terms = (
        KApply('f', args),
        KApply('f', *args),
        KApply('f', args=args),
        KApply(label='f', args=args),
    )

    # Then
    for term in terms:
        assert term.label == KLabel('f')
        assert term.args == tuple(args)


@pytest.mark.parametrize('args', KAPPLY_TEST_DATA[1:], ids=count())
def test_kapply_init_multiple_values(args: list[KInner]) -> None:
    # Given
    expected_message = 'KApply() got multiple values for argument: args'

    with pytest.raises(TypeError) as excinfo:
        # When
        KApply('f', *args, args=args)  # type: ignore

    actual_message = str(excinfo.value)

    # Then
    assert actual_message == expected_message


@pytest.mark.parametrize('args', KAPPLY_TEST_DATA, ids=count())
def test_kapply_init_unkown_keyword(args: list[KInner]) -> None:
    # Given
    expected_message = 'KApply() got an unexpected keyword argument: key'

    with pytest.raises(TypeError) as excinfo:
        # When
        KApply('f', *args, key='value')  # type: ignore

    actual_message = str(excinfo.value)

    # Then
    assert actual_message == expected_message


KSEQUENCE_TEST_DATA: Final[tuple[list[KInner], ...]] = (
    [],
    [x],
    [x, y],
    [x, y, z],
)


@pytest.mark.parametrize('items', KSEQUENCE_TEST_DATA, ids=count())
def test_ksequence_init(items: list[KInner]) -> None:
    # When
    terms = (
        KSequence(items),
        KSequence(*items),
        KSequence(items=items),
    )

    # Then
    for term in terms:
        assert term.items == tuple(items)


@pytest.mark.parametrize('items', KSEQUENCE_TEST_DATA[1:], ids=count())
def test_ksequence_init_multiple_values(items: list[KInner]) -> None:
    # Given
    expected_message = 'KSequence() got multiple values for argument: items'

    with pytest.raises(TypeError) as excinfo:
        # When
        KSequence(*items, items=items)  # type: ignore

    actual_message = str(excinfo.value)

    # Then
    assert actual_message == expected_message


@pytest.mark.parametrize('items', KSEQUENCE_TEST_DATA, ids=count())
def test_ksequence_init_unkown_keyword(items: list[KInner]) -> None:
    # Given
    expected_message = 'KSequence() got an unexpected keyword argument: key'

    with pytest.raises(TypeError) as excinfo:
        # When
        KSequence(*items, key='value')  # type: ignore

    actual_message = str(excinfo.value)

    # Then
    assert actual_message == expected_message


def test_defn_module_names() -> None:
    # Given
    defn = KDefinition(
        'FOO',
        [
            KFlatModule('BAR', [], []),
            KFlatModule('FOO', [], [KImport('FOO-A'), KImport('FOO-B')]),
            KFlatModule('FOO-A', [], [KImport('FOO-C')]),
            KFlatModule('FOO-B', [], [KImport('FOO-C')]),
            KFlatModule('FOO-C', [], []),
        ],
    )

    # Then
    assert len(defn.all_module_names) == 5
    assert len(defn.module_names) == 4
    assert set(defn.all_module_names) == {'FOO', 'BAR', 'FOO-A', 'FOO-B', 'FOO-C'}
    assert set(defn.module_names) == {'FOO', 'FOO-A', 'FOO-B', 'FOO-C'}


_0: Final = token('0')
BUILD_ASSOC_TEST_DATA: Final = (
    ((_0,), _0),
    ((x,), x),
    ((x, _0), x),
    ((_0, x), x),
    ((x, y), f(x, y)),
    ((_0, x, y), f(x, y)),
    ((x, _0, y), f(x, y)),
    ((x, y, _0), f(x, y)),
    ((x, y, z), f(x, f(y, z))),
    ((_0, x, y, z), f(x, f(y, z))),
    ((x, _0, y, z), f(x, f(y, z))),
    ((x, y, _0, z), f(x, f(y, z))),
    ((x, y, z, _0), f(x, f(y, z))),
    ((_0, x, _0, y, _0, z, _0), f(x, f(y, z))),
)


@pytest.mark.parametrize('terms,expected', BUILD_ASSOC_TEST_DATA, ids=count())
def test_build_assoc(terms: tuple[KInner, ...], expected: KInner) -> None:
    # When
    actual = build_assoc(_0, f, terms)

    # Then
    assert actual == expected


KAST_COMPARE_TEST_DATA: Final = (
    (KVariable('X', sort=KSort('Int')), KVariable('X', sort=KSort('Int')), False),
    (KVariable('X', sort=KSort('Int')), KVariable('X'), False),
    (KVariable('X'), KVariable('X', sort=KSort('Int')), True),
    (KVariable('X', sort=KSort('Int')), KVariable('Y', sort=KSort('Int')), True),
    (KVariable('X', sort=KSort('Int')), KVariable('Y'), True),
    (KVariable('X'), KVariable('Y', sort=KSort('Int')), True),
)


@pytest.mark.parametrize('lkast,rkast,expected', KAST_COMPARE_TEST_DATA, ids=count())
def test_kast_compare(lkast: KInner, rkast: KInner, expected: bool) -> None:
    actual = lkast < rkast
    assert actual == expected


IS_PREFIX_TEST_DATA: Final = (
    (KProduction('Int'), False),
    (KProduction('Int', (KTerminal('foo'),)), False),
    (KProduction('Int', (KNonTerminal(KSort('Foo')),)), False),
    (KProduction('Int', (KTerminal('foo'), KTerminal('('))), False),
    (KProduction('Int', (KTerminal('foo'), KTerminal('('), KTerminal(')'))), True),
    (KProduction('Int', (KRegexTerminal('foo', '', ''), KTerminal('('), KTerminal(')'))), False),
    (KProduction('Int', (KNonTerminal(KSort('foo')), KTerminal('('), KTerminal(')'))), False),
    (KProduction('Int', (KTerminal('foo'), KTerminal('bar'), KTerminal('('), KTerminal(')'))), True),
    (KProduction('Int', (KTerminal('foo'), KTerminal('('), KNonTerminal(KSort('Foo')), KTerminal(')'))), True),
    (
        KProduction(
            'Int',
            (
                KTerminal('foo'),
                KTerminal('('),
                KNonTerminal(KSort('Foo')),
                KTerminal(','),
                KTerminal(')'),
            ),
        ),
        False,
    ),
    (
        KProduction(
            'Int',
            (
                KTerminal('foo'),
                KTerminal('('),
                KNonTerminal(KSort('Foo')),
                KTerminal(','),
                KNonTerminal(KSort('Bar')),
                KTerminal(')'),
            ),
        ),
        True,
    ),
)


@pytest.mark.parametrize('production,expected', IS_PREFIX_TEST_DATA, ids=count())
def test_production_is_prefix(production: KProduction, expected: bool) -> None:
    # When
    actual = production.is_prefix

    # Then
    assert actual == expected


S = KSort('S')
DEFAULT_FORMAT_TEST_DATA: Final = (
    (KProduction(S), ''),
    (KProduction(S, (KTerminal('foo'),)), '%1'),
    (KProduction(S, (KTerminal('foo'), KTerminal('bar'))), '%1 %2'),
    (KProduction(S, (KTerminal('foo'), KTerminal('bar'), KTerminal('baz'))), '%1 %2 %3'),
    (KProduction(S, (KTerminal('foo'), KNonTerminal(S), KTerminal('baz'))), '%1 %2 %3'),
    (KProduction(S, (KTerminal('foo'), KTerminal('('), KTerminal(')'))), '%1 %2 %3'),
    (KProduction(S, (KTerminal('foo'), KTerminal('('), KNonTerminal(S), KTerminal(')'))), '%1 %2 %3 %4'),
    (KProduction(S, (KTerminal('foo'), KTerminal('('), KNonTerminal(S, 'x'), KTerminal(')'))), '%1 %2... x: %3 %4'),
    (
        KProduction(
            S, (KTerminal('foo'), KTerminal('('), KNonTerminal(S, 'x'), KTerminal(','), KNonTerminal(S), KTerminal(')'))
        ),
        '%1 %2 %3 %4 %5 %6',
    ),
    (
        KProduction(
            S,
            (
                KTerminal('foo'),
                KTerminal('('),
                KNonTerminal(S, 'x'),
                KTerminal(','),
                KNonTerminal(S, 'y'),
                KTerminal(')'),
            ),
        ),
        '%1 %2... x: %3 %4 y: %5 %6',
    ),
)


@pytest.mark.parametrize('production,format_str', DEFAULT_FORMAT_TEST_DATA, ids=count())
def test_default_format(production: KProduction, format_str: str) -> None:
    # Given
    expected = Format.parse(format_str)

    # When
    actual = production.default_format

    # Then
    assert actual == expected


S, S1, S2, T, U = (KSort(name) for name in ['S', 'S1', 'S2', 'T', 'U'])
PRODUCTION_APPLY_TEST_DATA: Final = (
    (
        KProduction(T, (KTerminal('foo'),), (), KLabel('foo')),
        KLabel('foo'),
        KProduction(T, (KTerminal('foo'),), (), KLabel('foo')),
    ),
    (
        KProduction(T, (KNonTerminal(S),), (), KLabel('foo')),
        KLabel('foo'),
        KProduction(T, (KNonTerminal(S),), (), KLabel('foo')),
    ),
    (
        KProduction(S, (KTerminal('foo'),), (S,), KLabel('foo', (S,))),
        KLabel('foo', (T,)),
        KProduction(T, (KTerminal('foo'),), (), KLabel('foo', (T,))),
    ),
    (
        KProduction(S, (KTerminal('foo'),), (S,), KLabel('foo', (S,))),
        KLabel('foo', (T,)),
        KProduction(T, (KTerminal('foo'),), (), KLabel('foo', (T,))),
    ),
    (
        KProduction(S1, (KTerminal('foo'), KNonTerminal(S2), KNonTerminal(S2)), (S1, S2), KLabel('foo', (S1, S2))),
        KLabel('foo', (T, U)),
        KProduction(T, (KTerminal('foo'), KNonTerminal(U), KNonTerminal(U)), (), KLabel('foo', (T, U))),
    ),
)


@pytest.mark.parametrize('production,klabel,expected', PRODUCTION_APPLY_TEST_DATA, ids=count())
def test_production_apply(production: KProduction, klabel: KLabel, expected: KProduction) -> None:
    # When
    actual = production.apply(klabel)

    # Then
    assert actual == expected
