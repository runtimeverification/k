from __future__ import annotations

import subprocess
from abc import ABC, abstractmethod
from enum import Enum
from typing import ClassVar  # noqa: TC003
from typing import TYPE_CHECKING

import pytest

from pyk.proof.reachability import APRProver

from ..cterm import CTermSymbolic
from ..kast.outer import read_kast_definition
from ..kcfg import KCFGExplore
from ..kllvm.compiler import compile_runtime, generate_hints
from ..kllvm.importer import import_runtime
from ..kore.kompiled import KompiledKore
from ..kore.pool import KoreServerPool
from ..kore.rpc import BoosterServer, KoreClient, KoreServer
from ..ktool import TypeInferenceMode
from ..ktool.kompile import DefinitionInfo, Kompile, LLVMKompileType
from ..ktool.kprint import KPrint
from ..ktool.kprove import KProve
from ..ktool.krun import KRun

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable, Iterator
    from pathlib import Path
    from typing import Any

    from pytest import FixtureRequest, TempPathFactory

    from ..kast.outer import KDefinition
    from ..kcfg.semantics import KCFGSemantics
    from ..kllvm.hints.prooftrace import KoreHeader
    from ..kllvm.runtime import Runtime
    from ..ktool.kprint import SymbolTable
    from ..utils import BugReport


class Kompiler:
    _path: Path
    _k_dir: Path
    _k_file_cache: dict[str, Path]
    _cache: dict[Kompile, Path]

    def __init__(self, tmp_path_factory: TempPathFactory):
        self._path = tmp_path_factory.mktemp('kompiled')
        self._k_dir = self._path / 'k-files'
        self._k_file_cache = {}
        self._cache = {}

    def __call__(
        self,
        *,
        # kompile file
        main_file: str | Path | None = None,
        # kompile text
        definition: str | None = None,
        main_module: str | None = None,
        **kwargs: Any,
    ) -> Path:
        if (main_file is None) == (definition is None):
            raise ValueError('Exactly one of main_file and definition must be set')

        if definition is not None:
            if main_module is None:
                raise ValueError('If definition is set, then main_module must be specified')
            main_file = self._cache_definition(definition)

        kwargs['main_file'] = main_file
        kwargs['main_module'] = main_module
        kompile = Kompile.from_dict(kwargs)
        if kompile not in self._cache:
            output_dir = self._path / self._uid(kompile)
            self._cache[kompile] = kompile(
                output_dir=output_dir,
                type_inference_mode=TypeInferenceMode.CHECKED,
                warnings_to_errors=True,
            )

        return self._cache[kompile]

    def _uid(self, kompile: Kompile) -> str:
        return f'{kompile.base_args.main_file.stem}-{kompile.backend.value}-{len(self._cache)}'

    def _cache_definition(self, definition: str) -> Path:
        definition = definition.strip()  # TODO preserve indentation
        if definition not in self._k_file_cache:
            self._k_dir.mkdir(exist_ok=True)
            main_file = self._k_dir / f'definition-{len(self._k_file_cache)}.k'
            main_file.write_text(definition)
            self._k_file_cache[definition] = main_file

        return self._k_file_cache[definition]


class KompiledTest:
    KOMPILE_MAIN_FILE: ClassVar[str | Path | None] = None
    KOMPILE_DEFINITION: ClassVar[str | None] = None
    KOMPILE_MAIN_MODULE: ClassVar[str | None] = None
    KOMPILE_BACKEND: ClassVar[str | None] = None
    KOMPILE_ARGS: ClassVar[dict[str, Any]] = {}

    @pytest.fixture(scope='class')
    def definition_dir(self, kompile: Kompiler) -> Path:
        kwargs = dict(self.KOMPILE_ARGS)
        kwargs['main_file'] = self.KOMPILE_MAIN_FILE
        kwargs['definition'] = self.KOMPILE_DEFINITION
        kwargs['main_module'] = self.KOMPILE_MAIN_MODULE
        kwargs['backend'] = self.KOMPILE_BACKEND
        return kompile(**kwargs)

    @pytest.fixture(scope='class')
    def definition(self, definition_dir: Path) -> KDefinition:
        return read_kast_definition(definition_dir / 'compiled.json')

    @pytest.fixture(scope='class')
    def kompiled_kore(self, definition_dir: Path) -> KompiledKore:
        return KompiledKore.load(definition_dir)

    @pytest.fixture(scope='class')
    def definition_info(self, definition_dir: Path) -> DefinitionInfo:
        return DefinitionInfo(definition_dir)


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


class UseServer(Enum):
    LEGACY = 'legacy'
    BOOSTER = 'booster'
    BOTH = 'both'
    NONE = 'none'


class ServerType(Enum):
    LEGACY = 'legacy'
    BOOSTER = 'booster'

    def enabled(self, use_server: UseServer) -> bool:
        match use_server:
            case UseServer.LEGACY:
                return self is ServerType.LEGACY
            case UseServer.BOOSTER:
                return self is ServerType.BOOSTER
            case UseServer.BOTH:
                return True
            case UseServer.NONE:
                return False
            case _:
                raise AssertionError()


class KoreServerTest(KompiledTest):
    DISABLE_LEGACY: ClassVar = False
    DISABLE_BOOSTER: ClassVar = False
    KOMPILE_BACKEND: ClassVar = 'haskell'

    LLVM_ARGS: ClassVar[dict[str, Any]] = {}

    @pytest.fixture(scope='class', params=['legacy', 'booster'])
    def server_type(self, request: FixtureRequest, use_server: UseServer) -> ServerType:
        res = ServerType(request.param)
        if not res.enabled(use_server):
            pytest.skip(f'Server is disabled globally: {res.value}')
        if (res is ServerType.LEGACY and self.DISABLE_LEGACY) or (res is ServerType.BOOSTER and self.DISABLE_BOOSTER):
            pytest.skip(f'Server is disabled for this test: {res.value}')
        return res

    @pytest.fixture(scope='class')
    def llvm_dir(self, server_type: ServerType, kompile: Kompiler) -> Path | None:
        if server_type is not ServerType.BOOSTER:
            return None

        kwargs = dict(self.LLVM_ARGS)
        kwargs['backend'] = 'llvm'
        kwargs['main_file'] = self.KOMPILE_MAIN_FILE
        kwargs['definition'] = self.KOMPILE_DEFINITION
        kwargs['main_module'] = self.KOMPILE_MAIN_MODULE
        kwargs['llvm_kompile_type'] = LLVMKompileType.C
        return kompile(**kwargs)

    @pytest.fixture
    def _kore_server(
        self,
        server_type: ServerType,
        definition_dir: Path,
        definition_info: DefinitionInfo,
        llvm_dir: Path | None,
        bug_report: BugReport | None,
    ) -> Iterator[KoreServer]:
        match server_type:
            case ServerType.LEGACY:
                assert not llvm_dir
                with KoreServer(
                    {
                        'kompiled_dir': definition_dir,
                        'module_name': definition_info.main_module_name,
                        'bug_report': bug_report,
                    }
                ) as server:
                    yield server
            case ServerType.BOOSTER:
                assert llvm_dir
                with BoosterServer(
                    {
                        'kompiled_dir': definition_dir,
                        'llvm_kompiled_dir': llvm_dir,
                        'module_name': definition_info.main_module_name,
                        'bug_report': bug_report,
                    }
                ) as server:
                    yield server
            case _:
                raise AssertionError


class KoreClientTest(KoreServerTest):
    CLIENT_TIMEOUT: ClassVar = 1000

    # definition_dir should ideally depend on server_type to avoid triggering kompilation,
    # but it can't due to method signature in superclass.
    # In the parameter list, always put `definition_dir` after `kore_client`.
    @pytest.fixture
    def kore_client(self, _kore_server: KoreServer, bug_report: BugReport) -> Iterator[KoreClient]:
        with KoreClient('localhost', _kore_server.port, timeout=self.CLIENT_TIMEOUT, bug_report=bug_report) as client:
            yield client


class CTermSymbolicTest(KoreClientTest):
    @pytest.fixture
    def cterm_symbolic(
        self,
        kore_client: KoreClient,
        definition: KDefinition,
        bug_report: BugReport | None,
    ) -> CTermSymbolic:
        return CTermSymbolic(kore_client, definition)


class KCFGExploreTest(CTermSymbolicTest):
    @abstractmethod
    def semantics(self, definition: KDefinition) -> KCFGSemantics: ...

    @pytest.fixture
    def kcfg_explore(
        self,
        cterm_symbolic: CTermSymbolic,
        bug_report: BugReport | None,
    ) -> Iterator[KCFGExplore]:
        semantics = self.semantics(cterm_symbolic._definition)
        yield KCFGExplore(cterm_symbolic, kcfg_semantics=semantics)


class ParallelTest(KoreServerTest, ABC):
    CLIENT_TIMEOUT: ClassVar = 1000

    @abstractmethod
    def semantics(self, definition: KDefinition) -> KCFGSemantics: ...

    def create_kore_client(self, _kore_server: KoreServer, bug_report: BugReport | None) -> KoreClient:
        return KoreClient('localhost', _kore_server.port, timeout=self.CLIENT_TIMEOUT, bug_report=bug_report)

    @pytest.fixture
    def create_prover(
        self,
        _kore_server: KoreServer,
        definition: KDefinition,
        bug_report: BugReport | None,
    ) -> Callable[[int, Iterable[str]], APRProver]:
        def _create_prover(max_depth: int, cut_point_rules: Iterable[str]) -> APRProver:
            kore_client = self.create_kore_client(_kore_server, bug_report)
            ct_symb = CTermSymbolic(kore_client, definition)
            _kcfg_explore = KCFGExplore(ct_symb, kcfg_semantics=self.semantics(definition))
            return APRProver(kcfg_explore=_kcfg_explore, execute_depth=max_depth, cut_point_rules=cut_point_rules)

        return _create_prover


class KoreServerPoolTest(KompiledTest, ABC):
    KOMPILE_BACKEND = 'haskell'

    POOL_MODULE_NAME: ClassVar[str]
    POOL_MAX_WORKERS: ClassVar[int | None] = None

    @pytest.fixture
    def create_server(self, definition_dir: Path) -> Callable[[], KoreServer]:
        def _create_server() -> KoreServer:
            return KoreServer({'kompiled_dir': definition_dir, 'module_name': self.POOL_MODULE_NAME})

        return _create_server

    @pytest.fixture
    def server_pool(self, create_server: Callable[[], KoreServer]) -> Iterator[KoreServerPool]:
        with KoreServerPool(create_server, max_workers=self.POOL_MAX_WORKERS) as pool:
            yield pool


class RuntimeTest(KompiledTest):
    KOMPILE_BACKEND = 'llvm'

    @pytest.fixture(scope='class')
    def runtime(self, definition_dir: Path) -> Runtime:
        compile_runtime(definition_dir)
        return import_runtime(definition_dir)


class ProofTraceTest(KompiledTest):
    KOMPILE_BACKEND = 'llvm'
    KOMPILE_ARGS = {'llvm_proof_hint_instrumentation': True}

    HINTS_INPUT_KORE: ClassVar[str]

    @pytest.fixture(scope='class')
    def hints(self, definition_dir: Path, kompile: Kompiler) -> bytes:
        input_kore_file = kompile._cache_definition(self.HINTS_INPUT_KORE)
        hints_file = generate_hints(definition_dir, input_kore_file)
        return hints_file.read_bytes()

    @pytest.fixture(scope='class')
    def header(self, definition_dir: Path) -> KoreHeader:
        process = subprocess.run(['kore-rich-header', str(definition_dir / 'definition.kore')], stdout=subprocess.PIPE)
        hdr = process.stdout
        header_file_name = definition_dir.name + '.header'
        path = definition_dir / header_file_name
        with path.open('wb') as f:
            f.write(hdr)
        from ..kllvm.hints.prooftrace import KoreHeader

        return KoreHeader.create(path)

    @pytest.fixture(scope='class')
    def definition_file(self, definition_dir: Path) -> str:
        definition_path = definition_dir / 'definition.kore'
        assert definition_path.is_file()
        with open(definition_path) as f:
            return f.read()

    @pytest.fixture(scope='class')
    def hints_file(self, definition_dir: Path, kompile: Kompiler) -> Path:
        input_kore_file = kompile._cache_definition(self.HINTS_INPUT_KORE)
        hints_file_name = definition_dir.name.replace('.k', '.hints')
        hints_file = generate_hints(definition_dir, input_kore_file, None, hints_file_name)
        return hints_file
