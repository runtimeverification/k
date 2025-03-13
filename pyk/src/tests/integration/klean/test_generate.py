from __future__ import annotations

from subprocess import CalledProcessError
from typing import TYPE_CHECKING

import pytest

from pyk import klean
from pyk.kore.internal import KoreDefn
from pyk.kore.parser import KoreParser
from pyk.utils import run_process_2

if TYPE_CHECKING:
    from pathlib import Path

    from pyk.testing import Kompiler


@pytest.fixture
def imp_defn(kompile: Kompiler) -> KoreDefn:
    from ..utils import K_FILES

    definition_dir = kompile(main_file=K_FILES / 'imp.k')
    kore_text = (definition_dir / 'definition.kore').read_text()
    definition = KoreParser(kore_text).definition()
    defn = KoreDefn.from_definition(definition)
    defn = defn.project_to_rewrites()
    return defn


@pytest.fixture
def skip_if_no_lake() -> None:
    try:
        run_process_2(['which', 'lean'])
    except CalledProcessError:
        pytest.skip('lean not installed')


def test_generate(
    skip_if_no_lake: None,
    imp_defn: KoreDefn,
    tmp_path: Path,
) -> None:
    project_dir = klean.generate(
        defn=imp_defn,
        output_dir=tmp_path,
        context={
            'package_name': 'klean-imp',
            'library_name': 'KLeanImp',
        },
        config={
            'derive_beq': True,
            'derive_decidableeq': True,
        },
    )

    proc_res = run_process_2(['lake', 'build'], cwd=project_dir, check=False)
    if proc_res.returncode:
        pytest.fail(proc_res.stdout)
