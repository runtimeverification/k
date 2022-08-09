import os
import shutil
from abc import ABC, abstractmethod
from itertools import chain
from pathlib import Path
from typing import Iterable

from pyk.ktool import KProve

from ..kast import KInner
from ..ktool import KProve
from ..prelude import mlTop
from .kompiled_test import KompiledTest


class KProveTest(KompiledTest, ABC):
    KPROVE_USE_DIR: str = '.kprove'
    KPROVE_INCLUDE_DIRS: Iterable[str] = []

    def setUp(self):
        super().setUp()

        shutil.rmtree(self.KPROVE_USE_DIR, ignore_errors=True)
        os.makedirs(self.KPROVE_USE_DIR)

        self.assertTrue(all(Path(include_dir).is_dir() for include_dir in self.KPROVE_INCLUDE_DIRS))

        kompiled_main_file = Path(self.KOMPILE_MAIN_FILE)
        kprove_main_file = kompiled_main_file.name
        kprove_include_dirs = [str(kompiled_main_file.parent)] + list(self.KPROVE_INCLUDE_DIRS)

        self.kprove = KProve(self.kompiled_dir, kprove_main_file, Path(self.KPROVE_USE_DIR))
        self.kprove.prover_args += list(chain.from_iterable(['-I', include_dir] for include_dir in kprove_include_dirs))
        self._update_symbol_table(self.kprove.symbol_table)

    def tearDown(self):
        shutil.rmtree(self.KPROVE_USE_DIR, ignore_errors=True)
        super().tearDown()

    @staticmethod
    @abstractmethod
    def _update_symbol_table(symbol_table):
        pass
