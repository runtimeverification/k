import logging
import shlex
from enum import Enum
from pathlib import Path
from subprocess import CalledProcessError
from typing import Final, Iterable, List, Optional

from ..cli_utils import abs_or_rel_to, check_dir_path, check_file_path, run_process

_LOGGER: Final = logging.getLogger(__name__)


class KompileBackend(Enum):
    LLVM = 'llvm'
    HASKELL = 'haskell'
    KORE = 'kore'
    JAVA = 'java'


def kompile(
    main_file: Path,
    *,
    command: Iterable[str] = ('kompile',),
    output_dir: Optional[Path] = None,
    backend: Optional[KompileBackend] = None,
    main_module: Optional[str] = None,
    syntax_module: Optional[str] = None,
    include_dirs: Iterable[Path] = (),
    md_selector: Optional[str] = None,
    hook_namespaces: Iterable[str] = (),
    emit_json: bool = True,
    post_process: Optional[str] = None,
    concrete_rules: Iterable[str] = (),
    # ---
    cwd: Optional[Path] = None,
    check: bool = True,
    profile: bool = False,
) -> Path:
    check_file_path(abs_or_rel_to(main_file, cwd or Path()))

    include_dirs = list(include_dirs)
    for include_dir in include_dirs:
        check_dir_path(abs_or_rel_to(include_dir, cwd or Path()))

    args = _build_arg_list(
        command=command,
        main_file=main_file,
        output_dir=output_dir,
        backend=backend,
        main_module=main_module,
        syntax_module=syntax_module,
        include_dirs=include_dirs,
        md_selector=md_selector,
        hook_namespaces=hook_namespaces,
        emit_json=emit_json,
        post_process=post_process,
        concrete_rules=concrete_rules,
    )

    try:
        run_process(args, logger=_LOGGER, cwd=cwd, check=check, profile=profile)
    except CalledProcessError as err:
        raise RuntimeError(
            f'Command kompile exited with code {err.returncode} for: {main_file}', err.stdout, err.stderr
        ) from err

    kompiled_dir = _kompiled_dir(main_file, output_dir)
    assert kompiled_dir.is_dir()
    return kompiled_dir


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
    post_process: Optional[str],
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

    if post_process:
        args.extend(['--post-process', shlex.quote(post_process)])

    if concrete_rules:
        args.extend(['--concrete-rules', ','.join(concrete_rules)])

    return args


def _kompiled_dir(main_file: Path, output_dir: Optional[Path] = None) -> Path:
    if output_dir:
        return output_dir

    return Path(main_file.stem + '-kompiled')
