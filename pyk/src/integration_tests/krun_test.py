import os
import shutil
from abc import ABC, abstractmethod
from pathlib import Path
from typing import Iterable, Optional

from pyk.ktool import KRun
from pyk.ktool.kprint import SymbolTable

from .kompiled_test import KompiledTest


class KRunTest(KompiledTest, ABC):
    KRUN_USE_DIR: Optional[str] = '.krun'
    KRUN_INCLUDE_DIRS: Iterable[str] = []

    def setUp(self) -> None:
        super().setUp()

        if self.KRUN_USE_DIR:
            shutil.rmtree(self.KRUN_USE_DIR, ignore_errors=True)
            os.makedirs(self.KRUN_USE_DIR)

            self.krun = KRun(self.kompiled_dir, use_directory=Path(self.KRUN_USE_DIR))
        else:
            self.krun = KRun(self.kompiled_dir)

    def tearDown(self) -> None:
        if self.KRUN_USE_DIR:
            shutil.rmtree(self.KRUN_USE_DIR, ignore_errors=True)
        super().tearDown()

    @staticmethod
    @abstractmethod
    def _update_symbol_table(symbol_table: SymbolTable) -> None:
        pass
