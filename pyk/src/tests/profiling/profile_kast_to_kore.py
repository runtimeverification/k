from __future__ import annotations

import sys
from typing import TYPE_CHECKING

from pyk.kast import KInner
from pyk.kast.inner import KSort
from pyk.kast.outer import read_kast_definition
from pyk.konvert import kast_to_kore, kore_to_kast

from .utils import TEST_DATA_DIR

if TYPE_CHECKING:
    from pathlib import Path

    from pyk.testing import Profiler


def test_kast_to_kore(profile: Profiler, tmp_path: Path) -> None:
    kast_to_kore_dir = TEST_DATA_DIR / 'kast-to-kore'
    definition_file = kast_to_kore_dir / 'compiled.json'
    kinner_file = kast_to_kore_dir / 'kinner.json'

    sys.setrecursionlimit(10**8)

    with profile('init-defn.prof', sort_keys=('cumtime',), limit=50):
        definition = read_kast_definition(definition_file)

    kast = KInner.from_json(kinner_file.read_text())

    for file_name in ['kast-to-kore-1.prof', 'kast-to-kore-2.prof']:
        with profile(file_name, sort_keys=('cumtime',), limit=25):
            kore = kast_to_kore(definition, kast, sort=KSort('GeneratedTopCell'))

    with profile('kore-to-kast.prof', sort_keys=('cumtime',), limit=25):
        kore_to_kast(definition, kore)
