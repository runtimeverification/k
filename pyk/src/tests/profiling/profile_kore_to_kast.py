from __future__ import annotations

import json
from typing import TYPE_CHECKING

from pyk.konvert import _kore_to_kast
from pyk.kore.syntax import Pattern

from .utils import TEST_DATA_DIR

if TYPE_CHECKING:
    from pyk.testing import Profiler


def test_kore_to_kast(profile: Profiler) -> None:
    json_file = TEST_DATA_DIR / 'kore-to-kast' / 'mir-semantics-295.json'
    json_data = json.loads(json_file.read_text())

    with profile('json-to-kore.prof', sort_keys=('cumtime',), limit=50):
        pattern = Pattern.from_dict(json_data)

    with profile('kore-to-kast.prof', sort_keys=('cumtime',), limit=50):
        _kore_to_kast(pattern)
