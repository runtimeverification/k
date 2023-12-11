from __future__ import annotations

__all__ = ['KompileBackend', 'kompile']

import dataclasses
import logging
import shlex
import shutil
from abc import ABC, abstractmethod
from dataclasses import dataclass
from enum import Enum
from functools import cached_property
from pathlib import Path
from subprocess import CalledProcessError
from typing import TYPE_CHECKING, final

from ..utils import abs_or_rel_to, check_dir_path, check_file_path, run_process

if TYPE_CHECKING:
    from collections.abc import Iterable, Mapping
    from typing import Any, Final, Literal

    from ..utils import BugReport

_LOGGER: Final = logging.getLogger(__name__)


class KompileNotFoundError(RuntimeError):
    def __init__(self, kompile_command: str):
        super().__init__(f'Kompile command not found: {str}')


class TypeInferenceMode(Enum):
    Z3 = 'z3'
    SIMPLESUB = 'simplesub'
    CHECKED = 'checked'
    DEFAULT = 'default'


def kompile(
    main_file: str | Path,
    *,
    command: Iterable[str] = ('kompile',),
    output_dir: str | Path | None = None,
    temp_dir: str | Path | None = None,
    type_inference_mode: str | TypeInferenceMode | None = None,
    debug: bool = False,
    verbose: bool = False,
    cwd: Path | None = None,
    check: bool = True,
    **kwargs: Any,
) -> Path:
    kwargs['main_file'] = main_file
    kompiler = Kompile.from_dict(kwargs)
    return kompiler(
        command=command,
        output_dir=output_dir,
        temp_dir=temp_dir,
        type_inference_mode=type_inference_mode,
        debug=debug,
        verbose=verbose,
        cwd=cwd,
        check=check,
    )


class KompileBackend(Enum):
    LLVM = 'llvm'
    HASKELL = 'haskell'
    KORE = 'kore'
    MAUDE = 'maude'

    @cached_property
    def args(self) -> frozenset[str]:
        match self:
            case KompileBackend.LLVM:
                return frozenset(field.name for field in dataclasses.fields(LLVMKompile) if field.name != 'base_args')
            case KompileBackend.HASKELL:
                return frozenset(
                    field.name for field in dataclasses.fields(HaskellKompile) if field.name != 'base_args'
                )
            case _:
                raise ValueError(f'Method not supported for backend: {self.value}')


class Kompile(ABC):
    base_args: KompileArgs

    @staticmethod
    def from_dict(dct: Mapping[str, Any]) -> Kompile:
        backend = KompileBackend(dct.get('backend') or 'llvm')

        common_args: dict[str, Any] = {}
        backend_args: dict[str, Any] = {}
        for key, value in dct.items():
            if key == 'backend':
                continue
            elif key in COMMON_ARGS:
                common_args[key] = value
            elif key in backend.args:
                backend_args[key] = value
            else:
                raise ValueError(f'Unexpected argument for backend: {backend.value}: {key}={value!r}')

        base_args = KompileArgs(**common_args)
        match backend:
            case KompileBackend.HASKELL:
                return HaskellKompile(base_args, **backend_args)
            case KompileBackend.LLVM:
                return LLVMKompile(base_args, **backend_args)
            case KompileBackend.MAUDE:
                return MaudeKompile(base_args, **backend_args)
            case _:
                raise ValueError(f'Unsupported backend: {backend.value}')

    @property
    @abstractmethod
    def backend(self) -> KompileBackend:
        ...

    def __call__(
        self,
        command: Iterable[str] | None = None,
        *,
        output_dir: str | Path | None = None,
        temp_dir: str | Path | None = None,
        type_inference_mode: str | TypeInferenceMode | None = None,
        debug: bool = False,
        verbose: bool = False,
        cwd: Path | None = None,
        check: bool = True,
        bug_report: BugReport | None = None,
    ) -> Path:
        check_file_path(abs_or_rel_to(self.base_args.main_file, cwd or Path()))
        for include_dir in self.base_args.include_dirs:
            check_dir_path(abs_or_rel_to(include_dir, cwd or Path()))

        command = list(command) if command is not None else ['kompile']
        if not shutil.which(command[0]):
            raise KompileNotFoundError(command[0])
        args = command + self.args()

        if output_dir is not None:
            output_dir = Path(output_dir)
            args += ['--output-definition', str(output_dir)]

        if temp_dir is not None:
            temp_dir = Path(temp_dir)
            args += ['--temp-dir', str(temp_dir)]

        if type_inference_mode is not None:
            type_inference_mode = TypeInferenceMode(type_inference_mode)
            args += ['--type-inference-mode', type_inference_mode.value]

        if debug:
            args += ['--debug']

        if verbose:
            args += ['--verbose']

        try:
            proc_res = run_process(args, logger=_LOGGER, cwd=cwd, check=check)
        except CalledProcessError as err:
            raise RuntimeError(
                f'Command kompile exited with code {err.returncode} for: {self.base_args.main_file}',
                err.stdout,
                err.stderr,
                err.returncode,
            ) from err

        if proc_res.stdout:
            out = proc_res.stdout.rstrip()
            print(out)
            if bug_report:
                bug_report.add_file_contents(out, Path('kompile.log'))

        definition_dir = output_dir if output_dir else Path(self.base_args.main_file.stem + '-kompiled')
        assert definition_dir.is_dir()

        return definition_dir

    @abstractmethod
    def args(self) -> list[str]:
        ...


@final
@dataclass(frozen=True)
class HaskellKompile(Kompile):
    base_args: KompileArgs
    concrete_rules: tuple[str, ...]
    haskell_binary: bool

    def __init__(self, base_args: KompileArgs, *, concrete_rules: Iterable[str] = (), haskell_binary: bool = True):
        concrete_rules = tuple(concrete_rules)
        object.__setattr__(self, 'base_args', base_args)
        object.__setattr__(self, 'concrete_rules', concrete_rules)
        object.__setattr__(self, 'haskell_binary', haskell_binary)

    @property
    def backend(self) -> Literal[KompileBackend.HASKELL]:
        return KompileBackend.HASKELL

    def args(self) -> list[str]:
        args = self.base_args.args()
        args += ['--backend', 'haskell']

        if self.concrete_rules:
            args += ['--concrete-rules', ','.join(self.concrete_rules)]

        if not self.haskell_binary:
            args += ['--no-haskell-binary']

        return args


@final
@dataclass(frozen=True)
class MaudeKompile(Kompile):
    base_args: KompileArgs

    def __init__(self, base_args: KompileArgs):
        object.__setattr__(self, 'base_args', base_args)

    @property
    def backend(self) -> Literal[KompileBackend.MAUDE]:
        return KompileBackend.MAUDE

    def args(self) -> list[str]:
        args = self.base_args.args()
        args += ['--backend', 'maude']

        return args


class LLVMKompileType(Enum):
    MAIN = 'main'
    SEARCH = 'search'
    LIBRARY = 'library'
    STATIC = 'static'
    PYTHON = 'python'
    C = 'c'


@final
@dataclass(frozen=True)
class LLVMKompile(Kompile):
    base_args: KompileArgs
    llvm_kompile_type: LLVMKompileType
    llvm_kompile_output: str | None
    opt_level: int
    ccopts: tuple[str, ...]
    no_llvm_kompile: bool
    enable_search: bool
    enable_llvm_debug: bool

    def __init__(
        self,
        base_args: KompileArgs,
        *,
        llvm_kompile_type: str | LLVMKompileType | None = None,
        llvm_kompile_output: str | None = None,
        opt_level: int | None = None,
        ccopts: Iterable[str] = (),
        no_llvm_kompile: bool = False,
        enable_search: bool = False,
        enable_llvm_debug: bool = False,
    ):
        llvm_kompile_type = LLVMKompileType(llvm_kompile_type) if llvm_kompile_type is not None else None

        opt_level = opt_level or 0
        if not (0 <= opt_level <= 3):
            raise ValueError('Invalid optimization level: {opt_level}')

        ccopts = tuple(ccopts)

        object.__setattr__(self, 'base_args', base_args)
        object.__setattr__(self, 'llvm_kompile_type', llvm_kompile_type)
        object.__setattr__(self, 'llvm_kompile_output', llvm_kompile_output)
        object.__setattr__(self, 'opt_level', opt_level)
        object.__setattr__(self, 'ccopts', ccopts)
        object.__setattr__(self, 'no_llvm_kompile', no_llvm_kompile)
        object.__setattr__(self, 'enable_search', enable_search)
        object.__setattr__(self, 'enable_llvm_debug', enable_llvm_debug)

    @property
    def backend(self) -> Literal[KompileBackend.LLVM]:
        return KompileBackend.LLVM

    def args(self) -> list[str]:
        args = self.base_args.args()
        args += ['--backend', 'llvm']

        if self.llvm_kompile_type:
            args += ['--llvm-kompile-type', self.llvm_kompile_type.value]

        if self.llvm_kompile_output is not None:
            args += ['--llvm-kompile-output', self.llvm_kompile_output]

        if self.opt_level:
            args += [f'-O{self.opt_level}']

        for ccopt in self.ccopts:
            args += ['-ccopt', ccopt]

        if self.no_llvm_kompile:
            args += ['--no-llvm-kompile']

        if self.enable_search:
            args += ['--enable-search']

        if self.enable_llvm_debug:
            args += ['--enable-llvm-debug']

        return args


@final
@dataclass(frozen=True)
class KompileArgs:
    main_file: Path
    main_module: str | None
    syntax_module: str | None
    include_dirs: tuple[Path, ...]
    md_selector: str | None
    hook_namespaces: tuple[str, ...]
    emit_json: bool
    gen_bison_parser: bool
    bison_parser_library: bool
    post_process: str | None
    read_only: bool

    def __init__(
        self,
        main_file: str | Path,
        *,
        main_module: str | None = None,
        syntax_module: str | None = None,
        include_dirs: Iterable[str | Path] = (),
        md_selector: str | None = None,
        hook_namespaces: Iterable[str] = (),
        emit_json: bool = True,
        gen_bison_parser: bool = False,
        bison_parser_library: bool = False,
        post_process: str | None = None,
        read_only: bool = False,
    ):
        main_file = Path(main_file)
        include_dirs = tuple(sorted(Path(include_dir) for include_dir in include_dirs))
        hook_namespaces = tuple(hook_namespaces)

        object.__setattr__(self, 'main_file', main_file)
        object.__setattr__(self, 'main_module', main_module)
        object.__setattr__(self, 'syntax_module', syntax_module)
        object.__setattr__(self, 'include_dirs', include_dirs)
        object.__setattr__(self, 'md_selector', md_selector)
        object.__setattr__(self, 'hook_namespaces', hook_namespaces)
        object.__setattr__(self, 'emit_json', emit_json)
        object.__setattr__(self, 'gen_bison_parser', gen_bison_parser)
        object.__setattr__(self, 'bison_parser_library', bison_parser_library)
        object.__setattr__(self, 'post_process', post_process)
        object.__setattr__(self, 'read_only', read_only)

    def args(self) -> list[str]:
        args = [str(self.main_file)]

        if self.main_module:
            args += ['--main-module', self.main_module]

        if self.syntax_module:
            args += ['--syntax-module', self.syntax_module]

        for include_dir in self.include_dirs:
            args += ['-I', str(include_dir)]

        if self.md_selector:
            args += ['--md-selector', self.md_selector]

        if self.hook_namespaces:
            args += ['--hook-namespaces', ' '.join(self.hook_namespaces)]

        if self.emit_json:
            args += ['--emit-json']

        if self.gen_bison_parser:
            args += ['--gen-bison-parser']

        if self.bison_parser_library:
            args += ['--bison-parser-library']

        if self.post_process:
            args += ['--post-process', shlex.quote(self.post_process)]

        if self.read_only:
            args += ['--read-only-kompiled-directory']

        return args


COMMON_ARGS: Final = frozenset(field.name for field in dataclasses.fields(KompileArgs))


@final
@dataclass(frozen=True)
class DefinitionInfo:
    path: Path

    def __init__(self, path: str | Path):
        path = Path(path)
        check_dir_path(path)
        object.__setattr__(self, 'path', path)

    @cached_property
    def backend(self) -> KompileBackend:
        backend = (self.path / 'backend.txt').read_text()
        return KompileBackend(backend)

    @cached_property
    def main_module_name(self) -> str:
        return (self.path / 'mainModule.txt').read_text()

    @cached_property
    def syntax_module_name(self) -> str:
        return (self.path / 'mainSyntaxModule.txt').read_text()

    @cached_property
    def timestamp(self) -> int:
        return (self.path / 'timestamp').stat().st_mtime_ns
