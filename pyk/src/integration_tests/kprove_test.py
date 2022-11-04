import shutil
from abc import ABC, abstractmethod
from itertools import chain
from pathlib import Path
from tempfile import mkdtemp
from typing import Iterable

from pyk.ktool import KProve
from pyk.ktool.kprint import SymbolTable

from .kompiled_test import KompiledTest
from .utils import free_port_on_host


class KProveTest(KompiledTest, ABC):
    KPROVE_INCLUDE_DIRS: Iterable[str] = []

    use_dir: Path
    kprove: KProve

    def setUp(self) -> None:
        super().setUp()

        self.assertTrue(all(Path(include_dir).is_dir() for include_dir in self.KPROVE_INCLUDE_DIRS))

        self.use_dir = Path(mkdtemp())
        kompiled_main_file = Path(self.KOMPILE_MAIN_FILE)
        kprove_main_file = Path(kompiled_main_file.name)
        kprove_include_dirs = [str(kompiled_main_file.parent)] + list(self.KPROVE_INCLUDE_DIRS)

        self.kprove = KProve(self.kompiled_dir, kprove_main_file, self.use_dir, port=free_port_on_host())
        self.kprove.prover_args += list(chain.from_iterable(['-I', include_dir] for include_dir in kprove_include_dirs))
        self._update_symbol_table(self.kprove.symbol_table)

    def tearDown(self) -> None:
        self.kprove.close_kore_rpc()
        shutil.rmtree(self.use_dir, ignore_errors=True)
        super().tearDown()

    @staticmethod
    @abstractmethod
    def _update_symbol_table(symbol_table: SymbolTable) -> None:
        pass
