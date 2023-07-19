from __future__ import annotations

from abc import ABC
from typing import TYPE_CHECKING

import pytest

from ..kast.outer import read_kast_definition
from ..kcfg import KCFGExplore
from ..kllvm.compiler import compile_runtime
from ..kllvm.importer import import_runtime
from ..kore.pool import KoreServerPool
from ..kore.rpc import KoreClient, KoreServer
from ..ktool.kompile import Kompile
from ..ktool.kprint import KPrint
from ..ktool.kprove import KProve
from ..ktool.krun import KRun

if TYPE_CHECKING:
    from collections.abc import Callable, Iterator
    from pathlib import Path
    from types import ModuleType
    from typing import Any, ClassVar

    from pytest import TempPathFactory

    from ..kast.outer import KDefinition
    from ..ktool.kprint import SymbolTable
    from ..utils import BugReport


class Kompiler:
    _path: Path
    _cache: dict[Kompile, Path]

    def __init__(self, tmp_path_factory: TempPathFactory):
        self._path = tmp_path_factory.mktemp('kompiled')
        self._cache = {}

    def __call__(self, main_file: str | Path, **kwargs: Any) -> Path:
        kwargs['main_file'] = main_file
        kompile = Kompile.from_dict(kwargs)
        if kompile not in self._cache:
            output_dir = self._path / self._uid(kompile)
            self._cache[kompile] = kompile(output_dir=output_dir)

        return self._cache[kompile]

    def _uid(self, kompile: Kompile) -> str:
        return f'{kompile.base_args.main_file.stem}-{kompile.backend.value}-{len(self._cache)}'


class KompiledTest:
    KOMPILE_MAIN_FILE: ClassVar[str | Path]
    KOMPILE_BACKEND: ClassVar[str | None] = None
    KOMPILE_ARGS: ClassVar[dict[str, Any]] = {}

    @pytest.fixture
    def bug_report(self, tmp_path: Path) -> BugReport | None:
        return None
        # Use the following line instead to generate bug reports for tests
        # return BugReport(tmp_path / 'bug-report')

    @pytest.fixture(scope='class')
    def definition_dir(self, kompile: Kompiler) -> Path:
        kwargs = self.KOMPILE_ARGS
        kwargs['main_file'] = self.KOMPILE_MAIN_FILE
        kwargs['backend'] = self.KOMPILE_BACKEND
        return kompile(**kwargs)

    @pytest.fixture(scope='class')
    def definition(self, definition_dir: Path) -> KDefinition:
        return read_kast_definition(definition_dir / 'compiled.json')


class KPrintTest(KompiledTest):
    @pytest.fixture
    def kprint(self, definition_dir: Path, tmp_path: Path) -> KPrint:
        use_directory = tmp_path / 'kprint'
        use_directory.mkdir()

        return KPrint(
            definition_dir,
            use_directory=use_directory,
            patch_symbol_table=self._update_symbol_table,
        )

    @staticmethod
    def _update_symbol_table(symbol_table: SymbolTable) -> None:
        pass


class KRunTest(KompiledTest):
    @pytest.fixture
    def krun(self, definition_dir: Path, tmp_path: Path) -> KRun:
        use_directory = tmp_path / 'krun'
        use_directory.mkdir()

        return KRun(
            definition_dir,
            use_directory=use_directory,
            patch_symbol_table=self._update_symbol_table,
        )

    @staticmethod
    def _update_symbol_table(symbol_table: SymbolTable) -> None:
        pass


class KProveTest(KompiledTest):
    KOMPILE_BACKEND = 'haskell'

    @pytest.fixture
    def kprove(self, definition_dir: Path, tmp_path: Path, bug_report: BugReport | None) -> KProve:
        use_directory = tmp_path / 'kprove'
        use_directory.mkdir()

        return KProve(
            definition_dir,
            use_directory=use_directory,
            bug_report=bug_report,
            patch_symbol_table=self._update_symbol_table,
        )

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


class KoreClientTest(KompiledTest):
    KOMPILE_BACKEND = 'haskell'

    KORE_MODULE_NAME: ClassVar[str]
    KORE_CLIENT_TIMEOUT: ClassVar = 1000

    @pytest.fixture
    def kore_client(self, definition_dir: Path, bug_report: BugReport) -> Iterator[KoreClient]:
        server = KoreServer(definition_dir, self.KORE_MODULE_NAME, bug_report=bug_report)
        client = KoreClient('localhost', server.port, timeout=self.KORE_CLIENT_TIMEOUT, bug_report=bug_report)
        yield client
        client.close()
        server.close()


class KoreServerPoolTest(KompiledTest, ABC):
    KOMPILE_BACKEND = 'haskell'

    POOL_MODULE_NAME: ClassVar[str]
    POOL_MAX_WORKERS: ClassVar[int | None] = None

    @pytest.fixture
    def create_server(self, definition_dir: Path) -> Callable[[], KoreServer]:
        def _create_server() -> KoreServer:
            return KoreServer(definition_dir, self.POOL_MODULE_NAME)

        return _create_server

    @pytest.fixture
    def server_pool(self, create_server: Callable[[], KoreServer]) -> Iterator[KoreServerPool]:
        with KoreServerPool(create_server, max_workers=self.POOL_MAX_WORKERS) as pool:
            yield pool


class RuntimeTest(KompiledTest):
    KOMPILE_BACKEND = 'llvm'

    @pytest.fixture(scope='class')
    def runtime(self, definition_dir: Path) -> ModuleType:
        compile_runtime(definition_dir)
        return import_runtime(definition_dir)
