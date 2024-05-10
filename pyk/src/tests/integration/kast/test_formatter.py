from __future__ import annotations

import textwrap
from itertools import count
from typing import TYPE_CHECKING

import pytest

from pyk.kast.formatter import Formatter
from pyk.kast.inner import KApply, KSequence, KSort, KToken, KVariable
from pyk.prelude.utils import token
from pyk.testing import KompiledTest

from ..utils import K_FILES

if TYPE_CHECKING:
    from pyk.kast import KInner
    from pyk.kast.outer import KDefinition


x, y = (KToken(name, KSort('Id')) for name in ['x', 'y'])


TEST_DATA = (
    (
        KApply('<k>', KSequence()),
        """
        <k>
          .K
        </k>
        """,
    ),
    (
        KApply('<k>', KSequence(KVariable('X'))),
        """
        <k>
          X ~> .K
        </k>
        """,
    ),
    (
        KApply(
            '<generatedTop>',
            KApply(
                '<T>',
                KApply(
                    '<k>',
                    KSequence(
                        KApply(
                            'while(_)_',
                            token(True),
                            KApply(
                                '{_}',
                                KApply(
                                    '__',
                                    KApply('_=_;', x, KApply('_+_', x, token(1))),
                                    KApply('_=_;', y, KApply('_-_', y, token(1))),
                                ),
                            ),
                        ),
                    ),
                ),
                KApply(
                    '<state>',
                    KApply(
                        '_Map_',
                        KApply('_|->_', x, token(0)),
                        KApply('_|->_', y, token(0)),
                    ),
                ),
            ),
            KApply('<generatedCounter>', token(0)),
        ),
        """
        <T>
          <k>
            while (true) {
              x = x + 1;
              y = y - 1;
            } ~> .K
          </k>
          <state>
            x |-> 0
            y |-> 0
          </state>
        </T>
        """,
    ),
)


class TestFormatter(KompiledTest):
    KOMPILE_MAIN_FILE = K_FILES / 'imp.k'

    @pytest.fixture
    def formatter(self, definition: KDefinition) -> Formatter:
        return Formatter(definition)

    @pytest.mark.parametrize('term,output', TEST_DATA, ids=count())
    def test(self, formatter: Formatter, term: KInner, output: str) -> None:
        # Given
        expected = textwrap.dedent(output).strip()

        # When
        actual = formatter(term)

        # Then
        assert actual == expected
