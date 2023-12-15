from __future__ import annotations

import json
from typing import TYPE_CHECKING

import pytest

from pyk.kast import KInner, kast_term
from pyk.kast.outer import KDefinition

from .utils import TEST_DATA_DIR

if TYPE_CHECKING:
    from pyk.kast import KAst
    from pyk.testing import Profiler


KAST_JSON_TEST_DATA: list[tuple[str, str, type]] = [
    ('kast-term', 'kast.json', KInner),
    ('compiled-defn', 'compiled.json', KDefinition),
]


@pytest.mark.parametrize(
    'test_id,file_name,cls', KAST_JSON_TEST_DATA, ids=[test_id for test_id, *_ in KAST_JSON_TEST_DATA]
)
def test_kast_json(profile: Profiler, test_id: str, file_name: str, cls: type) -> None:
    json_file = TEST_DATA_DIR / file_name
    json_text = json_file.read_text()

    with profile('json-parse.prof', sort_keys=('cumtime',), limit=20):
        json_data = json.loads(json_text)

    with profile('json-to-kast.prof', sort_keys=('cumtime',), limit=35):
        kast: KAst = cls.from_dict(kast_term(json_data))  # type: ignore

    with profile('kast-to-json.prof', sort_keys=('cumtime',), limit=35):
        kast.to_dict()
