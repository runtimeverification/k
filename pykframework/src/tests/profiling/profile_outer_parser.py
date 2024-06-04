from __future__ import annotations

from typing import TYPE_CHECKING

from pykframework.kast.markdown import select_code_blocks
from pykframework.kast.outer_lexer import outer_lexer
from pykframework.kast.outer_parser import OuterParser

from .utils import TEST_DATA_DIR

if TYPE_CHECKING:
    from pytest_mock import MockerFixture

    from pykframework.testing import Profiler


def test_outer_parser(profile: Profiler, mocker: MockerFixture) -> None:
    md_file = TEST_DATA_DIR / 'domains.md'
    md_text = md_file.read_text()

    with profile('markdown.prof', sort_keys=('cumtime', 'tottime'), limit=20):
        k_text = select_code_blocks(md_text, 'k')

    with profile('lexer.prof', sort_keys=('cumtime', 'tottime'), limit=30):
        tokens = list(outer_lexer(k_text))

    mock = mocker.patch('pykframework.kast.outer_parser.outer_lexer')
    mock.return_value = iter(tokens)
    parser = OuterParser('')
    mock.assert_called_with('')

    with profile('parser.prof', sort_keys=('cumtime', 'tottime'), limit=20):
        parser.definition()
