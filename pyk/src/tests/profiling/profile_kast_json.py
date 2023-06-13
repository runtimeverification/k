from __future__ import annotations

import json
from typing import TYPE_CHECKING

from pyk.kast import kast_term

from .utils import TEST_DATA_DIR

if TYPE_CHECKING:
    from pyk.kast import KAst
    from pyk.testing import Profiler


def test_kast_json(profile: Profiler) -> None:
    json_file = TEST_DATA_DIR / 'kast.json'
    with json_file.open() as f:
        json_data = json.load(f)

    with profile('json-to-kast.prof', sort_keys=('cumtime',), limit=20):
        kast: KAst = kast_term(json_data)

    with profile('kast-to-json.prof', sort_keys=('cumtime',), limit=20):
        kast.to_dict()
