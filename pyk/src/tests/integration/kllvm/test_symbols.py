def test_str(load_kllvm: None) -> None:
    from pyk.kllvm.ast import CompositeSort, Symbol

    # Given
    s1 = Symbol("Lbl'Plus")

    # When
    s1_str = str(s1)

    # Then
    assert s1_str == "Lbl'Plus{}"

    # And given
    s2 = Symbol("Lbl'Plus")
    s2.add_formal_argument(CompositeSort('A'))

    # When
    s2_str = str(s2)

    # Then
    assert s2_str == "Lbl'Plus{A{}}"


def test_equal(load_kllvm: None) -> None:
    from pyk.kllvm.ast import Symbol

    # Given
    a1 = Symbol('A')
    a2 = Symbol('A')
    b = Symbol('B')

    # Then
    assert a1 is not a2
    assert a1 == a2
    assert a1 != b


def test_variable(load_kllvm: None) -> None:
    from pyk.kllvm.ast import Variable

    # When
    a = Variable('A')

    # Then
    assert a.name == 'A'
    assert str(a) == 'A'
