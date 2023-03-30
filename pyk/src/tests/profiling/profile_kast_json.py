from __future__ import annotations

import json
from typing import TYPE_CHECKING

from pyk.kast import kast_term

from .utils import TEST_DATA_DIR

if TYPE_CHECKING:
    from .utils import Profiler


def test_kast_term(profile: Profiler) -> None:
    json_file = TEST_DATA_DIR / 'kast.json'
    with json_file.open() as f:
        json_data = json.load(f)

    with profile(sort_keys=('cumtime',), limit=20):
        kast_term(json_data)
