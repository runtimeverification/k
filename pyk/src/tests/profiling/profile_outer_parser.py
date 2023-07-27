from __future__ import annotations

from typing import TYPE_CHECKING

from pyk.kast.outer_lexer import outer_lexer
from pyk.kast.outer_parser import OuterParser

from .utils import TEST_DATA_DIR

if TYPE_CHECKING:
    from pytest_mock import MockerFixture

    from pyk.testing import Profiler


def test_outer_parser(profile: Profiler, mocker: MockerFixture) -> None:
    k_file = TEST_DATA_DIR / 'domains.k'
    k_text = k_file.read_text()

    with profile('lexer.prof', sort_keys=('cumtime', 'tottime'), limit=30):
        tokens = list(outer_lexer(k_text))

    mock = mocker.patch('pyk.kast.outer_parser.outer_lexer')
    mock.return_value = iter(tokens)
    parser = OuterParser('')
    mock.assert_called_with('')

    with profile('parser.prof', sort_keys=('cumtime', 'tottime'), limit=20):
        parser.definition()
