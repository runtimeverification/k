__all__ = ['KompileBackend', 'kompile', 'llvm_kompile', 'haskell_kompile']

import logging
import shlex
from enum import Enum
from pathlib import Path
from subprocess import CalledProcessError
from typing import Final, Iterable, List, Optional, Union

from ..cli_utils import abs_or_rel_to, check_dir_path, check_file_path, run_process

_LOGGER: Final = logging.getLogger(__name__)


class KompileBackend(Enum):
    LLVM = 'llvm'
    HASKELL = 'haskell'
    KORE = 'kore'
    JAVA = 'java'


def kompile(
    main_file: Union[str, Path],
    *,
    command: Iterable[str] = ('kompile',),
    output_dir: Optional[Union[str, Path]] = None,
    backend: Optional[Union[str, KompileBackend]] = None,
    main_module: Optional[str] = None,
    syntax_module: Optional[str] = None,
    include_dirs: Iterable[Union[str, Path]] = (),
    md_selector: Optional[str] = None,
    hook_namespaces: Iterable[str] = (),
    emit_json: bool = True,
    debug: bool = False,
    post_process: Optional[str] = None,
    # LLVM backend
    opt_level: Optional[int] = None,
    ccopts: Iterable[str] = (),
    no_llvm_kompile: bool = False,
    # Haskell backend
    concrete_rules: Iterable[str] = (),
    # ---
    cwd: Optional[Path] = None,
    check: bool = True,
) -> Path:
    main_file = Path(main_file)
    check_file_path(abs_or_rel_to(main_file, cwd or Path()))

    _include_dirs = [Path(include_dir) for include_dir in include_dirs]
    for include_dir in _include_dirs:
        check_dir_path(abs_or_rel_to(include_dir, cwd or Path()))

    backend = KompileBackend(backend) if backend is not None else None

    if backend and backend != KompileBackend.LLVM:
        _check_backend_param(opt_level is None, 'opt_level', backend)
        _check_backend_param(not list(ccopts), 'ccopts', backend)
        _check_backend_param(not no_llvm_kompile, 'no_llvm_kompile', backend)

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
        debug=debug,
        post_process=post_process,
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
    main_file: Union[str, Path],
    *,
    command: Iterable[str] = ('kompile',),
    output_dir: Optional[Union[str, Path]] = None,
    main_module: Optional[str] = None,
    syntax_module: Optional[str] = None,
    include_dirs: Iterable[Union[str, Path]] = (),
    md_selector: Optional[str] = None,
    hook_namespaces: Iterable[str] = (),
    emit_json: bool = True,
    debug: bool = False,
    post_process: Optional[str] = None,
    opt_level: Optional[int] = None,
    ccopts: Iterable[str] = (),
    no_llvm_kompile: bool = False,
    # ---
    cwd: Optional[Path] = None,
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
        debug=debug,
        post_process=post_process,
        opt_level=opt_level,
        ccopts=ccopts,
        no_llvm_kompile=no_llvm_kompile,
        cwd=cwd,
        check=check,
    )


def haskell_kompile(
    main_file: Union[str, Path],
    *,
    command: Iterable[str] = ('kompile',),
    output_dir: Optional[Union[str, Path]] = None,
    backend: Optional[KompileBackend] = None,
    main_module: Optional[str] = None,
    syntax_module: Optional[str] = None,
    include_dirs: Iterable[Union[str, Path]] = (),
    md_selector: Optional[str] = None,
    hook_namespaces: Iterable[str] = (),
    emit_json: bool = True,
    debug: bool = False,
    post_process: Optional[str] = None,
    concrete_rules: Iterable[str] = (),
    # ---
    cwd: Optional[Path] = None,
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
        debug=debug,
        post_process=post_process,
        concrete_rules=concrete_rules,
        cwd=cwd,
        check=check,
    )


def _check_backend_param(check: bool, param_name: str, backend: Optional[KompileBackend]) -> None:
    if not check:
        raise ValueError(f'Parameter not supported by backend {backend}: {param_name}')


def _build_arg_list(
    *,
    command: Iterable[str],
    main_file: Path,
    output_dir: Optional[Path],
    backend: Optional[KompileBackend],
    main_module: Optional[str],
    syntax_module: Optional[str],
    include_dirs: Iterable[Path],
    md_selector: Optional[str],
    hook_namespaces: Iterable[str],
    emit_json: bool,
    debug: bool = False,
    post_process: Optional[str],
    opt_level: Optional[int],
    ccopts: Iterable[str],
    no_llvm_kompile: bool,
    concrete_rules: Iterable[str],
) -> List[str]:
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

    if debug:
        args.append('--debug')

    if post_process:
        args.extend(['--post-process', shlex.quote(post_process)])

    if opt_level:
        args.append(f'-O{opt_level}')

    for ccopt in ccopts:
        args += ['-ccopt', ccopt]

    if no_llvm_kompile:
        args.append('--no-llvm-kompile')

    if concrete_rules:
        args.extend(['--concrete-rules', ','.join(concrete_rules)])

    return args
