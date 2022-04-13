import shutil
from abc import ABC
from pathlib import Path
from typing import Iterable, Optional
from unittest import TestCase

from pyk.ktool import KompileBackend, kompile


class KompiledTest(TestCase, ABC):
    KOMPILE_MAIN_FILE: str
    KOMPILE_BACKEND: Optional[KompileBackend] = None
    KOMPILE_OUTPUT_DIR: Optional[str] = None
    KOMPILE_INCLUDE_DIRS: Iterable[str] = []
    KOMPILE_EMIT_JSON = False

    def setUp(self):
        main_file = Path(self.KOMPILE_MAIN_FILE)
        self.assertTrue(main_file.is_file())
        self.assertEqual(main_file.suffix, '.k')

        output_dir = Path(self.KOMPILE_OUTPUT_DIR) if self.KOMPILE_OUTPUT_DIR else None

        include_dirs = [Path(include_dir) for include_dir in self.KOMPILE_INCLUDE_DIRS]
        self.assertTrue(all(include_dir.is_dir() for include_dir in include_dirs))

        self.kompiled_dir = kompile(
            main_file,
            backend=self.KOMPILE_BACKEND,
            output_dir=output_dir,
            include_dirs=include_dirs,
            emit_json=self.KOMPILE_EMIT_JSON,
        )

        self.assertTrue(self.kompiled_dir.is_dir())

    def tearDown(self):
        shutil.rmtree(self.kompiled_dir)
