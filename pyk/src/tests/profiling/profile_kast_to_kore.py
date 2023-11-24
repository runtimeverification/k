from __future__ import annotations

import sys
from typing import TYPE_CHECKING

from pyk.kast import KInner
from pyk.kast.inner import KSort
from pyk.kast.outer import read_kast_definition
from pyk.konvert import kast_to_kore, kore_to_kast
from pyk.kore.kompiled import KompiledKore

from .utils import TEST_DATA_DIR

if TYPE_CHECKING:
    from pathlib import Path

    from pyk.testing import Profiler


def test_kast_to_kore(profile: Profiler, tmp_path: Path) -> None:
    kast_to_kore_dir = TEST_DATA_DIR / 'kast-to-kore'
    kast_defn_file = kast_to_kore_dir / 'compiled.json'
    kinner_file = kast_to_kore_dir / 'kinner.json'

    sys.setrecursionlimit(10**8)

    with profile('init-kast-defn.prof', sort_keys=('cumtime',), limit=50):
        kast_defn = read_kast_definition(kast_defn_file)

    with profile('init-kore-defn.prof', sort_keys=('cumtime',), limit=50):
        kore_defn = KompiledKore.load(kast_to_kore_dir)  # first time from KORE

    kore_defn.write(tmp_path)
    with profile('reinit-kore-defn.prof', sort_keys=('cumtime',), limit=25):
        kore_defn = KompiledKore.load(tmp_path)  # second time from JSON

    kast = KInner.from_json(kinner_file.read_text())

    for file_name in ['kast-to-kore-1.prof', 'kast-to-kore-2.prof']:
        with profile(file_name, sort_keys=('cumtime',), limit=25):
            kore = kast_to_kore(kast_defn, kore_defn, kast, sort=KSort('GeneratedTopCell'))

    with profile('kore-to-kast.prof', sort_keys=('cumtime',), limit=25):
        kore_to_kast(kast_defn, kore)
