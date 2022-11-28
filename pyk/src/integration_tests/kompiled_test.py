import json
import shutil
from pathlib import Path
from tempfile import mkdtemp
from typing import ClassVar, Iterable, Optional
from unittest import TestCase

from pyk.cli_utils import check_dir_path, check_file_path
from pyk.kast.inner import KInner
from pyk.kast.outer import KDefinition
from pyk.ktool import KompileBackend, kompile
from pyk.prelude.ml import is_top


class KompiledTest(TestCase):
    KOMPILE_MAIN_FILE: ClassVar[str]
    KOMPILE_BACKEND: ClassVar[Optional[str]] = None
    KOMPILE_MAIN_MODULE: ClassVar[Optional[str]] = None
    KOMPILE_SYNTAX_MODULE: ClassVar[Optional[str]] = None
    KOMPILE_INCLUDE_DIRS: ClassVar[Iterable[str]] = []
    KOMPILE_POST_PROCESS: ClassVar[Optional[str]] = None

    kompiled_dir: ClassVar[Path]
    definition: ClassVar[KDefinition]

    @classmethod
    def setUpClass(cls) -> None:
        main_file = Path(cls.KOMPILE_MAIN_FILE)
        check_file_path(main_file)

        output_dir = Path(mkdtemp())
        include_dirs = [Path(include_dir) for include_dir in cls.KOMPILE_INCLUDE_DIRS]

        for include_dir in include_dirs:
            check_dir_path(include_dir)

        backend = KompileBackend(cls.KOMPILE_BACKEND) if cls.KOMPILE_BACKEND else None

        cls.kompiled_dir = kompile(
            main_file,
            output_dir=output_dir,
            backend=backend,
            main_module=cls.KOMPILE_MAIN_MODULE,
            syntax_module=cls.KOMPILE_SYNTAX_MODULE,
            include_dirs=include_dirs,
            post_process=cls.KOMPILE_POST_PROCESS,
        )

        with open(cls.kompiled_dir / 'compiled.json', 'r') as f:
            json_dct = json.load(f)
            cls.definition = KDefinition.from_dict(json_dct['term'])

    @classmethod
    def tearDownClass(cls) -> None:
        shutil.rmtree(cls.kompiled_dir, ignore_errors=True)

    def assertTop(self, term: KInner) -> None:  # noqa: N802
        self.assertTrue(is_top(term), f'{term} is not #Top')

    def assertNotTop(self, term: KInner) -> None:  # noqa: N802
        self.assertFalse(is_top(term), f'{term} is #Top')
