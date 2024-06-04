from __future__ import annotations

import sys
from typing import TYPE_CHECKING

from pykframework.kore.lexer import kore_lexer
from pykframework.kore.parser import KoreParser

from .utils import TEST_DATA_DIR

if TYPE_CHECKING:
    from pytest_mock import MockerFixture

    from pykframework.testing import Profiler


def test_kore_parse(profile: Profiler, mocker: MockerFixture) -> None:
    definition_file = TEST_DATA_DIR / 'definition.kore'
    definition_text = definition_file.read_text()

    sys.setrecursionlimit(10**8)

    with profile('lexer.prof', sort_keys=('cumtime', 'tottime'), limit=15):
        tokens = list(kore_lexer(definition_text))

    mock = mocker.patch('pykframework.kore.parser.kore_lexer')
    mock.return_value = iter(tokens)
    parser = KoreParser('')
    mock.assert_called_with('')

    with profile('parser.prof', sort_keys=('cumtime', 'tottime'), limit=75):
        parser.definition()
