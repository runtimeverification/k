import os
import shutil
from abc import ABC, abstractmethod
from pathlib import Path
from typing import Iterable

from pyk.ktool import KRun

from .kompiled_test import KompiledTest


class KRunTest(KompiledTest, ABC):
    KRUN_USE_DIR: str = '.krun'
    KRUN_INCLUDE_DIRS: Iterable[str] = []

    def setUp(self):
        super().setUp()

        shutil.rmtree(self.KRUN_USE_DIR, ignore_errors=True)
        os.makedirs(self.KRUN_USE_DIR)

        self.krun = KRun(self.kompiled_dir, use_directory=Path(self.KRUN_USE_DIR))

    def tearDown(self):
        shutil.rmtree(self.KRUN_USE_DIR, ignore_errors=True)
        super().tearDown()

    @staticmethod
    @abstractmethod
    def _update_symbol_table(symbol_table):
        pass
