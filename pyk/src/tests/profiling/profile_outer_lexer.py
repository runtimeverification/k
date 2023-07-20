from __future__ import annotations

from typing import TYPE_CHECKING

from pyk.kast.outer_lexer import outer_lexer

from .utils import TEST_DATA_DIR

if TYPE_CHECKING:
    from pyk.testing import Profiler


def test_outer_lexer(profile: Profiler) -> None:
    k_file = TEST_DATA_DIR / 'domains.k'
    k_text = k_file.read_text()

    with profile('outer-lexer.prof', sort_keys=('cumtime', 'tottime'), limit=30):
        list(outer_lexer(k_text))
