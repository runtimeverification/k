from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kast.outer import read_kast_definition
from pyk.kcfg import KCFGExplore
from pyk.ktool.kompile import KompileBackend, kompile
from pyk.ktool.kprint import KPrint
from pyk.ktool.kprove import KProve
from pyk.ktool.krun import KRun

if TYPE_CHECKING:
    from pathlib import Path
    from typing import ClassVar, Iterable, Iterator, Optional, Union

    from pytest import TempPathFactory

    from pyk.cli_utils import BugReport
    from pyk.kast.outer import KDefinition
    from pyk.ktool.kprint import SymbolTable


class Kompiler:
    _tmp_path_factory: TempPathFactory

    def __init__(self, tmp_path_factory: TempPathFactory):
        self._tmp_path_factory = tmp_path_factory

    def __call__(
        self,
        main_file: Union[str, Path],
        *,
        backend: Optional[Union[str, KompileBackend]] = None,
        main_module: Optional[str] = None,
        syntax_module: Optional[str] = None,
        include_dirs: Iterable[Union[str, Path]] = (),
    ) -> Path:
        return kompile(
            main_file=main_file,
            output_dir=self._tmp_path_factory.mktemp('kompiled'),
            backend=backend,
            main_module=main_module,
            syntax_module=syntax_module,
            include_dirs=include_dirs,
        )


class KompiledTest:
    KOMPILE_MAIN_FILE: ClassVar[str]
    KOMPILE_BACKEND: ClassVar[Optional[str]] = None
    KOMPILE_MAIN_MODULE: ClassVar[Optional[str]] = None
    KOMPILE_SYNTAX_MODULE: ClassVar[Optional[str]] = None
    KOMPILE_INCLUDE_DIRS: ClassVar[Iterable[str]] = []

    @pytest.fixture(scope='class')
    def bug_report(self) -> Optional[BugReport]:
        return None
        # Use the following line instead to generate bug reports for tests
        # return BugReport(Path('bug_report'))

    @pytest.fixture(scope='class')
    def definition_dir(self, kompile: Kompiler) -> Path:
        return kompile(
            main_file=self.KOMPILE_MAIN_FILE,
            backend=KompileBackend(self.KOMPILE_BACKEND) if self.KOMPILE_BACKEND else None,
            main_module=self.KOMPILE_MAIN_MODULE,
            syntax_module=self.KOMPILE_SYNTAX_MODULE,
            include_dirs=self.KOMPILE_INCLUDE_DIRS,
        )

    @pytest.fixture(scope='class')
    def definition(self, definition_dir: Path) -> KDefinition:
        return read_kast_definition(definition_dir / 'compiled.json')


class KPrintTest(KompiledTest):
    @pytest.fixture
    def kprint(self, definition_dir: Path, tmp_path_factory: TempPathFactory) -> KPrint:
        kprint = KPrint(definition_dir, use_directory=tmp_path_factory.mktemp('kprint'))
        self._update_symbol_table(kprint.symbol_table)
        return kprint

    @staticmethod
    def _update_symbol_table(symbol_table: SymbolTable) -> None:
        pass


class KRunTest(KompiledTest):
    @pytest.fixture
    def krun(self, definition_dir: Path, tmp_path_factory: TempPathFactory) -> KRun:
        krun = KRun(definition_dir, use_directory=tmp_path_factory.mktemp('krun'))
        self._update_symbol_table(krun.symbol_table)
        return krun

    @staticmethod
    def _update_symbol_table(symbol_table: SymbolTable) -> None:
        pass


class KProveTest(KompiledTest):
    KOMPILE_BACKEND = 'haskell'

    @pytest.fixture
    def kprove(
        self, definition_dir: Path, tmp_path_factory: TempPathFactory, bug_report: Optional[BugReport]
    ) -> KProve:
        kprove = KProve(definition_dir, use_directory=tmp_path_factory.mktemp('kprove'), bug_report=bug_report)
        self._update_symbol_table(kprove.symbol_table)
        return kprove

    @staticmethod
    def _update_symbol_table(symbol_table: SymbolTable) -> None:
        pass


class KCFGExploreTest(KProveTest):
    @pytest.fixture
    def kcfg_explore(self, kprove: KProve) -> Iterator[KCFGExplore]:
        with KCFGExplore(kprove, bug_report=kprove._bug_report) as kcfg_explore:
            yield kcfg_explore
