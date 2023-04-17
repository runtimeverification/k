from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING, NamedTuple

import pytest

from pyk.kast.outer import read_kast_definition
from pyk.kcfg import KCFGExplore
from pyk.ktool.kompile import KompileBackend, kompile
from pyk.ktool.kprint import KPrint
from pyk.ktool.kprove import KProve
from pyk.ktool.krun import KRun

if TYPE_CHECKING:
    from collections.abc import Iterable, Iterator
    from typing import Any, ClassVar

    from pytest import TempPathFactory

    from pyk.cli_utils import BugReport
    from pyk.kast.outer import KDefinition
    from pyk.ktool.kprint import SymbolTable


class Target(NamedTuple):
    main_file: Path
    backend: KompileBackend
    main_module: str | None
    syntax_module: str | None
    include_dirs: tuple[Path, ...]

    def as_dict(self) -> dict[str, Any]:
        return self._asdict()


class Kompiler:
    _path: Path
    _cache: dict[Target, Path]

    def __init__(self, tmp_path_factory: TempPathFactory):
        self._path = tmp_path_factory.mktemp('kompiled')
        self._cache = {}

    def __call__(
        self,
        main_file: str | Path,
        *,
        backend: str | KompileBackend | None = None,
        main_module: str | None = None,
        syntax_module: str | None = None,
        include_dirs: Iterable[str | Path] = (),
    ) -> Path:
        target = Target(
            main_file=Path(main_file).resolve(),
            backend=KompileBackend(backend) if backend is not None else KompileBackend.LLVM,
            main_module=main_module,
            syntax_module=syntax_module,
            include_dirs=tuple(sorted(Path(include_dir).resolve() for include_dir in include_dirs)),
        )

        if target not in self._cache:
            output_dir = self._path / self._uid(target)
            self._cache[target] = kompile(output_dir=output_dir, **target.as_dict())

        return self._cache[target]

    def _uid(self, target: Target) -> str:
        return f'{target.main_file.stem}-{target.backend.value}-{len(self._cache)}'


class KompiledTest:
    KOMPILE_MAIN_FILE: ClassVar[str]
    KOMPILE_BACKEND: ClassVar[str | None] = None
    KOMPILE_MAIN_MODULE: ClassVar[str | None] = None
    KOMPILE_SYNTAX_MODULE: ClassVar[str | None] = None
    KOMPILE_INCLUDE_DIRS: ClassVar[Iterable[str]] = []

    @pytest.fixture(scope='class')
    def bug_report(self) -> BugReport | None:
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
    def kprove(self, definition_dir: Path, tmp_path_factory: TempPathFactory, bug_report: BugReport | None) -> KProve:
        kprove = KProve(definition_dir, use_directory=tmp_path_factory.mktemp('kprove'), bug_report=bug_report)
        self._update_symbol_table(kprove.symbol_table)
        return kprove

    @staticmethod
    def _update_symbol_table(symbol_table: SymbolTable) -> None:
        pass


class KCFGExploreTest(KProveTest):
    @pytest.fixture
    def kcfg_explore(self, kprove: KProve) -> Iterator[KCFGExplore]:
        with KCFGExplore(
            kprove,
            bug_report=kprove._bug_report,
        ) as kcfg_explore:
            yield kcfg_explore
