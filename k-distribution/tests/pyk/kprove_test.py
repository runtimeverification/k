import os
import shutil
from abc import ABC, abstractmethod
from itertools import chain
from pathlib import Path
from typing import List
from unittest import TestCase

from pyk.ktool import KProve


class KProveTest(TestCase, ABC):
    DEFN_DIR: str
    MAIN_FILE_NAME: str
    USE_DIR: str
    INCLUDE_DIRS: List[str]

    def setUp(self):
        shutil.rmtree(self.USE_DIR, ignore_errors=True)
        os.makedirs(self.USE_DIR)

        self.assertTrue(Path(self.DEFN_DIR).is_dir())
        self.assertTrue(all(Path(include_dir).is_dir() for include_dir in self.INCLUDE_DIRS))

        self.kprove = KProve(self.DEFN_DIR, self.MAIN_FILE_NAME, self.USE_DIR)
        self.kprove.proverArgs += list(chain.from_iterable(['-I', include_dir] for include_dir in self.INCLUDE_DIRS))
        self._update_symbol_table(self.kprove.symbolTable)

    def tearDown(self):
        shutil.rmtree(self.USE_DIR, ignore_errors=True)

    @staticmethod
    @abstractmethod
    def _update_symbol_table(symbol_table):
        pass
