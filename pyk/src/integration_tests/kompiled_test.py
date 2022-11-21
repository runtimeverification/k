import json
import shutil
from pathlib import Path
from tempfile import mkdtemp
from typing import Iterable, Optional
from unittest import TestCase

from pyk.kast.inner import KInner
from pyk.kast.outer import KDefinition
from pyk.ktool import KompileBackend, kompile
from pyk.prelude.ml import is_top


class KompiledTest(TestCase):
    KOMPILE_MAIN_FILE: str
    KOMPILE_BACKEND: Optional[KompileBackend] = None
    KOMPILE_INCLUDE_DIRS: Iterable[str] = []
    KOMPILE_POST_PROCESS: Optional[str] = None

    kompiled_dir: Path
    definition: KDefinition

    def setUp(self) -> None:
        main_file = Path(self.KOMPILE_MAIN_FILE)
        self.assertTrue(main_file.is_file())
        self.assertEqual(main_file.suffix, '.k')

        output_dir = Path(mkdtemp())
        include_dirs = [Path(include_dir) for include_dir in self.KOMPILE_INCLUDE_DIRS]
        self.assertTrue(all(include_dir.is_dir() for include_dir in include_dirs))

        self.kompiled_dir = kompile(
            main_file,
            backend=self.KOMPILE_BACKEND,
            output_dir=output_dir,
            include_dirs=include_dirs,
            post_process=self.KOMPILE_POST_PROCESS,
        )

        with open(self.kompiled_dir / 'compiled.json', 'r') as f:
            json_dct = json.load(f)
            self.definition = KDefinition.from_dict(json_dct['term'])

    def tearDown(self) -> None:
        shutil.rmtree(self.kompiled_dir, ignore_errors=True)

    def assertTop(self, term: KInner) -> None:  # noqa: N802
        self.assertTrue(is_top(term), f'{term} is not #Top')

    def assertNotTop(self, term: KInner) -> None:  # noqa: N802
        self.assertFalse(is_top(term), f'{term} is #Top')
