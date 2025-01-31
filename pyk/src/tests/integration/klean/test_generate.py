from __future__ import annotations

from subprocess import CalledProcessError
from typing import TYPE_CHECKING

import pytest

from pyk import klean
from pyk.utils import run_process_2

if TYPE_CHECKING:
    from pathlib import Path

    from pyk.testing import Kompiler


@pytest.fixture
def imp_definition(kompile: Kompiler) -> Path:
    from ..utils import K_FILES

    return kompile(main_file=K_FILES / 'imp.k')


@pytest.fixture
def skip_if_no_lake() -> None:
    try:
        run_process_2(['which', 'lean'])
    except CalledProcessError:
        pytest.skip('lean not installed')


def test_generate(
    skip_if_no_lake: None,
    imp_definition: Path,
    tmp_path: Path,
) -> None:
    project_dir = klean.generate(
        definition_dir=imp_definition,
        output_dir=tmp_path,
        context={
            'package_name': 'klean-imp',
            'library_name': 'KLeanImp',
        },
    )

    proc_res = run_process_2(['lake', 'build'], cwd=project_dir, check=False)
    if proc_res.returncode:
        pytest.fail(proc_res.stdout)
