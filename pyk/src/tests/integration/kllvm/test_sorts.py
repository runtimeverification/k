def test_is_concrete(load_kllvm: None) -> None:
    from pyk.kllvm.ast import CompositeSort

    # Given
    sort = CompositeSort('A')

    # When
    actual = sort.is_concrete

    # Then
    assert actual


def test_is_not_concrete(load_kllvm: None) -> None:
    from pyk.kllvm.ast import SortVariable

    # Given
    sort = SortVariable('B')

    # When
    actual = sort.is_concrete

    # Then
    assert not actual


def test_name(load_kllvm: None) -> None:
    from pyk.kllvm.ast import CompositeSort

    # Given
    name = 'SortInt'

    # When
    sort = CompositeSort(name)

    # Then
    assert sort.name == name


def test_str(load_kllvm: None) -> None:
    from pyk.kllvm.ast import CompositeSort, SortVariable

    # Given
    s1 = CompositeSort('A')

    # When
    s1_str = str(s1)

    # Then
    assert s1_str == 'A{}'

    # And given
    s2 = SortVariable('B')

    # When
    s2_str = str(s2)

    # Then
    assert s2_str == 'B'


def test_add_argument(load_kllvm: None) -> None:
    from pyk.kllvm.ast import CompositeSort, SortVariable

    # Given
    f = CompositeSort('F')
    a = CompositeSort('A')
    b = SortVariable('B')

    # When
    f.add_argument(a)
    f.add_argument(b)

    # Then
    assert str(f) == 'F{A{},B}'


def test_substitution_1(load_kllvm: None) -> None:
    from pyk.kllvm.ast import CompositeSort, SortVariable

    # Given
    x = SortVariable('X')
    a = CompositeSort('A')
    expected = a

    # When
    actual = a.substitute({x: a})

    # Then
    assert actual == expected


def test_substitution_2(load_kllvm: None) -> None:
    from pyk.kllvm.ast import CompositeSort, SortVariable

    x = SortVariable('X')
    y = SortVariable('Y')
    a = CompositeSort('A')
    b = CompositeSort('B')
    c = CompositeSort('C')

    original = CompositeSort('F')
    g1 = CompositeSort('G')
    g1.add_argument(x)
    g1.add_argument(x)
    g1.add_argument(b)
    g1.add_argument(y)
    original.add_argument(g1)

    assert str(original) == 'F{G{X,X,B{},Y}}'
    assert not original.is_concrete

    expected = CompositeSort('F')
    g2 = CompositeSort('G')
    g2.add_argument(a)
    g2.add_argument(a)
    g2.add_argument(b)
    g2.add_argument(c)
    expected.add_argument(g2)

    assert str(expected), 'F{G{A{},A{},B{},C{}}}'
    assert expected.is_concrete

    # When
    actual = original.substitute({x: a, y: c})

    # Then
    assert actual == expected


def test_equality(load_kllvm: None) -> None:
    from pyk.kllvm.ast import CompositeSort, SortVariable

    # Given
    a1 = CompositeSort('A')
    a2 = CompositeSort('A')
    b1 = SortVariable('B')
    b2 = SortVariable('B')

    # Then
    assert a1 is not a2
    assert a1 == a2
    assert b1 is not b2
    assert b1 == b2
    assert a1 != b1
    assert a2 != b2
