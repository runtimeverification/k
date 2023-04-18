from __future__ import annotations

__all__ = ['KompileBackend', 'kompile', 'llvm_kompile', 'haskell_kompile']

import logging
import shlex
from enum import Enum
from pathlib import Path
from subprocess import CalledProcessError
from typing import TYPE_CHECKING

from ..cli_utils import abs_or_rel_to, check_dir_path, check_file_path, run_process

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Final

_LOGGER: Final = logging.getLogger(__name__)


class KompileBackend(Enum):
    LLVM = 'llvm'
    HASKELL = 'haskell'
    KORE = 'kore'


class LLVMKompileType(Enum):
    MAIN = 'main'
    SEARCH = 'search'
    LIBRARY = 'library'
    STATIC = 'static'
    PYTHON = 'python'
    C = 'c'


def kompile(
    main_file: str | Path,
    *,
    command: Iterable[str] = ('kompile',),
    output_dir: str | Path | None = None,
    backend: str | KompileBackend | None = None,
    main_module: str | None = None,
    syntax_module: str | None = None,
    include_dirs: Iterable[str | Path] = (),
    md_selector: str | None = None,
    hook_namespaces: Iterable[str] = (),
    emit_json: bool = True,
    gen_bison_parser: bool = False,
    bison_parser_library: bool = False,
    debug: bool = False,
    post_process: str | None = None,
    # LLVM backend
    llvm_kompile_type: LLVMKompileType | None = None,
    llvm_kompile_output: str | None = None,
    opt_level: int | None = None,
    ccopts: Iterable[str] = (),
    no_llvm_kompile: bool = False,
    enable_search: bool = False,
    # Haskell backend
    concrete_rules: Iterable[str] = (),
    # ---
    cwd: Path | None = None,
    check: bool = True,
) -> Path:
    main_file = Path(main_file)
    check_file_path(abs_or_rel_to(main_file, cwd or Path()))

    _include_dirs = [Path(include_dir) for include_dir in include_dirs]
    for include_dir in _include_dirs:
        check_dir_path(abs_or_rel_to(include_dir, cwd or Path()))

    backend = KompileBackend(backend) if backend is not None else None

    if backend and backend != KompileBackend.LLVM:
        _check_backend_param(llvm_kompile_type is None, 'llvm_kompile_type', backend)
        _check_backend_param(llvm_kompile_output is None, 'llvm_kompile_output', backend)
        _check_backend_param(opt_level is None, 'opt_level', backend)
        _check_backend_param(not list(ccopts), 'ccopts', backend)
        _check_backend_param(not no_llvm_kompile, 'no_llvm_kompile', backend)
        _check_backend_param(not enable_search, 'enable_search', backend)

    if backend != KompileBackend.HASKELL:
        _check_backend_param(not list(concrete_rules), 'concrete_rules', backend)

    if opt_level and not (0 <= opt_level <= 3):
        raise ValueError('Invalid optimization level: {opt_level}')

    output_dir = Path(output_dir) if output_dir is not None else None

    args = _build_arg_list(
        command=command,
        main_file=main_file,
        output_dir=output_dir,
        backend=backend,
        main_module=main_module,
        syntax_module=syntax_module,
        include_dirs=_include_dirs,
        md_selector=md_selector,
        hook_namespaces=hook_namespaces,
        emit_json=emit_json,
        gen_bison_parser=gen_bison_parser,
        bison_parser_library=bison_parser_library,
        debug=debug,
        post_process=post_process,
        llvm_kompile_type=llvm_kompile_type,
        llvm_kompile_output=llvm_kompile_output,
        enable_search=enable_search,
        opt_level=opt_level,
        ccopts=ccopts,
        no_llvm_kompile=no_llvm_kompile,
        concrete_rules=concrete_rules,
    )

    try:
        run_process(args, logger=_LOGGER, cwd=cwd, check=check)
    except CalledProcessError as err:
        raise RuntimeError(
            f'Command kompile exited with code {err.returncode} for: {main_file}',
            err.stdout,
            err.stderr,
            err.returncode,
        ) from err

    kompiled_dir = output_dir if output_dir else Path(main_file.stem + '-kompiled')
    assert kompiled_dir.is_dir()
    return kompiled_dir


def llvm_kompile(
    main_file: str | Path,
    *,
    command: Iterable[str] = ('kompile',),
    output_dir: str | Path | None = None,
    main_module: str | None = None,
    syntax_module: str | None = None,
    include_dirs: Iterable[str | Path] = (),
    md_selector: str | None = None,
    hook_namespaces: Iterable[str] = (),
    emit_json: bool = True,
    gen_bison_parser: bool = False,
    bison_parser_library: bool = False,
    debug: bool = False,
    post_process: str | None = None,
    llvm_kompile_type: LLVMKompileType | None = None,
    opt_level: int | None = None,
    ccopts: Iterable[str] = (),
    no_llvm_kompile: bool = False,
    enable_search: bool = False,
    # ---
    cwd: Path | None = None,
    check: bool = True,
) -> Path:
    return kompile(
        main_file=main_file,
        backend=KompileBackend.LLVM,
        command=command,
        output_dir=output_dir,
        main_module=main_module,
        syntax_module=syntax_module,
        include_dirs=include_dirs,
        md_selector=md_selector,
        hook_namespaces=hook_namespaces,
        emit_json=emit_json,
        gen_bison_parser=gen_bison_parser,
        bison_parser_library=bison_parser_library,
        debug=debug,
        post_process=post_process,
        opt_level=opt_level,
        ccopts=ccopts,
        no_llvm_kompile=no_llvm_kompile,
        enable_search=enable_search,
        llvm_kompile_type=llvm_kompile_type,
        cwd=cwd,
        check=check,
    )


def haskell_kompile(
    main_file: str | Path,
    *,
    command: Iterable[str] = ('kompile',),
    output_dir: str | Path | None = None,
    backend: KompileBackend | None = None,
    main_module: str | None = None,
    syntax_module: str | None = None,
    include_dirs: Iterable[str | Path] = (),
    md_selector: str | None = None,
    hook_namespaces: Iterable[str] = (),
    emit_json: bool = True,
    gen_bison_parser: bool = False,
    bison_parser_library: bool = False,
    debug: bool = False,
    post_process: str | None = None,
    concrete_rules: Iterable[str] = (),
    # ---
    cwd: Path | None = None,
    check: bool = True,
) -> Path:
    return kompile(
        main_file=main_file,
        backend=KompileBackend.HASKELL,
        command=command,
        output_dir=output_dir,
        main_module=main_module,
        syntax_module=syntax_module,
        include_dirs=include_dirs,
        md_selector=md_selector,
        hook_namespaces=hook_namespaces,
        emit_json=emit_json,
        gen_bison_parser=gen_bison_parser,
        bison_parser_library=bison_parser_library,
        debug=debug,
        post_process=post_process,
        concrete_rules=concrete_rules,
        cwd=cwd,
        check=check,
    )


def _check_backend_param(check: bool, param_name: str, backend: KompileBackend | None) -> None:
    if not check:
        raise ValueError(f'Parameter not supported by backend {backend}: {param_name}')


def _build_arg_list(
    *,
    command: Iterable[str],
    main_file: Path,
    output_dir: Path | None,
    backend: KompileBackend | None,
    main_module: str | None,
    syntax_module: str | None,
    include_dirs: Iterable[Path],
    md_selector: str | None,
    hook_namespaces: Iterable[str],
    emit_json: bool,
    gen_bison_parser: bool,
    bison_parser_library: bool,
    debug: bool = False,
    post_process: str | None,
    llvm_kompile_type: LLVMKompileType | None = None,
    llvm_kompile_output: str | None = None,
    opt_level: int | None,
    ccopts: Iterable[str],
    no_llvm_kompile: bool,
    enable_search: bool,
    concrete_rules: Iterable[str],
) -> list[str]:
    args = list(command) + [str(main_file)]

    if output_dir:
        args += ['--output-definition', str(output_dir)]

    if backend:
        args += ['--backend', backend.value]

    if main_module:
        args.extend(['--main-module', main_module])

    if syntax_module:
        args.extend(['--syntax-module', syntax_module])

    for include_dir in include_dirs:
        args += ['-I', str(include_dir)]

    if md_selector:
        args.extend(['--md-selector', md_selector])

    if hook_namespaces:
        args.extend(['--hook-namespaces', ' '.join(hook_namespaces)])

    if emit_json:
        args.append('--emit-json')

    if gen_bison_parser:
        args.append('--gen-bison-parser')

    if bison_parser_library:
        args.append('--bison-parser-library')

    if debug:
        args.append('--debug')

    if post_process:
        args.extend(['--post-process', shlex.quote(post_process)])

    if llvm_kompile_type is not None:
        args.extend(['--llvm-kompile-type', llvm_kompile_type.value])

    if llvm_kompile_output is not None:
        args.extend(['--llvm-kompile-output', llvm_kompile_output])

    if opt_level:
        args.append(f'-O{opt_level}')

    for ccopt in ccopts:
        args += ['-ccopt', ccopt]

    if no_llvm_kompile:
        args.append('--no-llvm-kompile')

    if enable_search:
        args.append('--enable-search')

    if concrete_rules:
        args.extend(['--concrete-rules', ','.join(concrete_rules)])

    return args
