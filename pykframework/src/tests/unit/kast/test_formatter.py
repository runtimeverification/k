from __future__ import annotations

import textwrap
from itertools import count
from typing import TYPE_CHECKING

import pytest

from pykframework.kast import KAtt
from pykframework.kast.att import Atts, Format
from pykframework.kast.formatter import Formatter
from pykframework.kast.inner import KLabel, KSort, KVariable
from pykframework.kast.outer import KDefinition, KFlatModule, KNonTerminal, KProduction, KTerminal
from pykframework.prelude.kint import INT
from pykframework.prelude.utils import token

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Final

    from pykframework.kast import KInner


add: Final = KLabel('_+_')
sub: Final = KLabel('_-_')
cell: Final = KLabel('<cell>')


def production(klabel: KLabel, sort: KSort, items: Iterable[KSort | str], formatt: str) -> KProduction:
    _items = tuple(KNonTerminal(item) if isinstance(item, KSort) else KTerminal(item) for item in items)
    return KProduction(sort=sort, items=_items, klabel=klabel, att=KAtt((Atts.FORMAT(Format.parse(formatt)),)))


S: Final = KSort('S')
DEFINITION: Final = KDefinition(
    main_module_name='TEST',
    all_modules=(
        KFlatModule(
            name='TEST',
            sentences=(
                production(cell, INT, ('<cell>', INT, '</cell>'), '%1%i%n%2%d%n%3'),
                production(add, INT, (INT, '+', INT), '%1 %2 %3'),
                production(sub, INT, (INT, '-', INT), '%1% %-% %3'),
            ),
        ),
    ),
)
TEST_DATA: Final = (
    (token(1), '1'),
    (KVariable('X'), 'X'),
    (KVariable('X', INT), 'X:Int'),
    (add(token(1), token(2)), '1 + 2'),
    (sub(token(1), token(2)), '1 - 2'),
    (add(add(token(1), token(2)), token(3)), '1 + 2 + 3'),
    (
        cell(token(1)),
        """
        <cell>
          1
        </cell>
        """,
    ),
    (
        cell(cell(token(1))),
        """
        <cell>
          <cell>
            1
          </cell>
        </cell>
        """,
    ),
)


@pytest.mark.parametrize('term,output', TEST_DATA, ids=count())
def test_formatter(term: KInner, output: str) -> None:
    # Given
    expected = textwrap.dedent(output).strip()
    formatter = Formatter(DEFINITION)

    # When
    actual = formatter(term)

    # Then
    assert actual == expected
