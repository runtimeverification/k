from itertools import count
from typing import Any, Dict, Final, List, Tuple

import pytest

from pyk.kast.inner import KApply, KInner, KLabel, KSequence, KSort, KVariable, build_assoc
from pyk.kast.outer import KDefinition, KFlatModule
from pyk.prelude.kbool import BOOL
from pyk.prelude.kint import INT
from pyk.prelude.string import STRING
from pyk.prelude.utils import token

from .utils import f, x, y, z

KVARIABLE_TEST_DATA: Final = (
    ('no-sort', KVariable('Foo'), {'node': 'KVariable', 'name': 'Foo', 'att': {'node': 'KAtt', 'att': {}}}),
    (
        'sort',
        KVariable('Foo', sort=KSort('Int')),
        {
            'node': 'KVariable',
            'name': 'Foo',
            'att': {'node': 'KAtt', 'att': {'org.kframework.kore.Sort': {'node': 'KSort', 'name': 'Int'}}},
        },
    ),
)


@pytest.mark.parametrize(
    'test_id,var,dct',
    KVARIABLE_TEST_DATA,
    ids=[test_id for test_id, *_ in KVARIABLE_TEST_DATA],
)
def test_kvariable_to_dict(test_id: str, var: KVariable, dct: Dict[str, Any]) -> None:
    # When
    actual_var = KVariable.from_dict(dct)
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


KLABEL_TEST_DATA: Final[Tuple[List[KSort], ...]] = (
    [],
    [BOOL],
    [BOOL, INT],
    [BOOL, INT, STRING],
)


@pytest.mark.parametrize('params', KLABEL_TEST_DATA, ids=count())
def test_klabel_init(params: List[KSort]) -> None:
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
def test_klabel_init_multiple_values(params: List[KSort]) -> None:
    # Given
    expected_message = "KLabel() got multiple values for argument 'params'"

    with pytest.raises(TypeError) as excinfo:
        # When
        KLabel('f', *params, params=params)  # type: ignore

    actual_message = str(excinfo.value)

    # Then
    actual_message, expected_message


@pytest.mark.parametrize('params', KLABEL_TEST_DATA, ids=count())
def test_klabel_init_unkown_keyword(params: List[KSort]) -> None:
    # Given
    expected_message = "KLabel() got an unexpected keyword argument 'key'"

    with pytest.raises(TypeError) as excinfo:
        # When
        KLabel('f', *params, key='value')  # type: ignore

    actual_message = str(excinfo.value)

    # Then
    assert actual_message == expected_message


KAPPLY_TEST_DATA: Final[Tuple[List[KInner], ...]] = (
    [],
    [x],
    [x, y],
    [x, y, z],
)


@pytest.mark.parametrize('args', KAPPLY_TEST_DATA, ids=count())
def test_kapply_init(args: List[KInner]) -> None:
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
def test_kapply_init_multiple_values(args: List[KInner]) -> None:
    # Given
    expected_message = "KApply() got multiple values for argument 'args'"

    with pytest.raises(TypeError) as excinfo:
        # When
        KApply('f', *args, args=args)  # type: ignore

    actual_message = str(excinfo.value)

    # Then
    assert actual_message == expected_message


@pytest.mark.parametrize('args', KAPPLY_TEST_DATA, ids=count())
def test_kapply_init_unkown_keyword(args: List[KInner]) -> None:
    # Given
    expected_message = "KApply() got an unexpected keyword argument 'key'"

    with pytest.raises(TypeError) as excinfo:
        # When
        KApply('f', *args, key='value')  # type: ignore

    actual_message = str(excinfo.value)

    # Then
    assert actual_message == expected_message


KSEQUENCE_TEST_DATA: Final[Tuple[List[KInner], ...]] = (
    [],
    [x],
    [x, y],
    [x, y, z],
)


@pytest.mark.parametrize('items', KSEQUENCE_TEST_DATA, ids=count())
def test_ksequence_init(items: List[KInner]) -> None:
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
def test_ksequence_init_multiple_values(items: List[KInner]) -> None:
    # Given
    expected_message = "KSequence() got multiple values for argument 'items'"

    with pytest.raises(TypeError) as excinfo:
        # When
        KSequence(*items, items=items)  # type: ignore

    actual_message = str(excinfo.value)

    # Then
    assert actual_message == expected_message


@pytest.mark.parametrize('items', KSEQUENCE_TEST_DATA, ids=count())
def test_ksequence_init_unkown_keyword(items: List[KInner]) -> None:
    # Given
    expected_message = "KSequence() got an unexpected keyword argument 'key'"

    with pytest.raises(TypeError) as excinfo:
        # When
        KSequence(*items, key='value')  # type: ignore

    actual_message = str(excinfo.value)

    # Then
    assert actual_message == expected_message


def test_defn_module_names() -> None:
    # Given
    defn = KDefinition('FOO', [KFlatModule('BAR', [], []), KFlatModule('FOO', [], [])])

    # Then
    assert set(defn.module_names) == {'FOO', 'BAR'}


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
def test_build_assoc(terms: Tuple[KInner, ...], expected: KInner) -> None:
    # When
    actual = build_assoc(_0, f, terms)

    # Then
    assert actual == expected
