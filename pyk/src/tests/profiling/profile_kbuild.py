from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kbuild import KBuild, Project

from .utils import TEST_DATA_DIR

if TYPE_CHECKING:
    from pathlib import Path
    from typing import Final

    from pyk.testing import Profiler


A_SEMANTICS_DIR: Final = TEST_DATA_DIR / 'kbuild/a-semantics'


@pytest.fixture
def kbuild(tmp_path: Path) -> KBuild:
    return KBuild(tmp_path / 'kbuild')


def test_kbuild(kbuild: KBuild, profile: Profiler) -> None:
    with profile('kompile.prof', sort_keys=('cumtime', 'tottime'), limit=35):
        project = Project.load_from_dir(A_SEMANTICS_DIR)
        kbuild.kompile(project, 'llvm')

    with profile('rekompile.prof', sort_keys=('cumtime', 'tottime'), limit=35):
        project = Project.load_from_dir(A_SEMANTICS_DIR)
        kbuild.kompile(project, 'llvm')
