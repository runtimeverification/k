from __future__ import annotations

import sys
from typing import TYPE_CHECKING

from pyk.kast import KInner
from pyk.kast.inner import KSort
from pyk.kast.outer import read_kast_definition
from pyk.konvert import kast_to_kore
from pyk.kore.kompiled import KompiledKore

from .utils import TEST_DATA_DIR

if TYPE_CHECKING:
    from .utils import Profiler


def test_kast_to_kore(profile: Profiler) -> None:
    kast_to_kore_dir = TEST_DATA_DIR / 'kast-to-kore'
    kast_defn_file = kast_to_kore_dir / 'compiled.json'
    kinner_file = kast_to_kore_dir / 'kinner.json'

    sys.setrecursionlimit(10**8)

    with profile('init-kast.txt', sort_keys=('cumtime',), limit=50):
        kast_defn = read_kast_definition(kast_defn_file)

    kore_defn = KompiledKore(kast_to_kore_dir)
    with profile('init-kore.txt', sort_keys=('cumtime',), limit=50):
        kore_defn.definition

    kast = KInner.from_json(kinner_file.read_text())

    for file_name in ['first.txt', 'second.txt']:
        with profile(file_name, sort_keys=('cumtime',), limit=25):
            kast_to_kore(kast_defn, kore_defn, kast, sort=KSort('GeneratedTopCell'))
