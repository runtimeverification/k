from __future__ import annotations

import sys
from typing import TYPE_CHECKING

from pyk.kore.parser import KoreParser

from .utils import TEST_DATA_DIR

if TYPE_CHECKING:
    from .utils import Profiler


def test_kore_parse(profile: Profiler) -> None:
    definition_file = TEST_DATA_DIR / 'definition.kore'
    definition_text = definition_file.read_text()
    parser = KoreParser(definition_text)

    sys.setrecursionlimit(10**8)

    with profile(sort_keys=('cumtime',), limit=50):
        parser.definition()
