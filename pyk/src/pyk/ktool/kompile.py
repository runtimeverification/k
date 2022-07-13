import logging
from enum import Enum
from pathlib import Path
from subprocess import CalledProcessError, CompletedProcess
from typing import Final, Iterable, List, Optional

from ..cli_utils import check_dir_path, check_file_path, run_process

_LOGGER: Final = logging.getLogger(__name__)


class KompileBackend(Enum):
    LLVM = 'llvm'
    HASKELL = 'haskell'
    KORE = 'kore'
    JAVA = 'java'


def kompile(
    main_file: Path,
    *,
    main_module: Optional[str] = None,
    syntax_module: Optional[str] = None,
    backend: Optional[KompileBackend],
    output_dir: Optional[Path] = None,
    include_dirs: Iterable[Path] = (),
    md_selector: Optional[str] = None,
    hook_namespaces: Iterable[str] = (),
    emit_json=False,
    concrete_rules: Iterable[str] = (),
    additional_args: Iterable[str] = (),
) -> Path:
    check_file_path(main_file)

    for include_dir in include_dirs:
        check_dir_path(include_dir)

    args = _build_arg_list(
        main_module=main_module,
        syntax_module=syntax_module,
        backend=backend,
        output_dir=output_dir,
        include_dirs=include_dirs,
        md_selector=md_selector,
        hook_namespaces=hook_namespaces,
        emit_json=emit_json,
        concrete_rules=concrete_rules,
        additional_args=additional_args
    )

    try:
        _kompile(str(main_file), *args)
    except CalledProcessError as err:
        raise RuntimeError(f'Command kompile exited with code {err.returncode} for: {main_file}', err.stdout, err.stderr)

    kompiled_dir = _kompiled_dir(main_file, output_dir)
    assert kompiled_dir.is_dir()
    return kompiled_dir


def _build_arg_list(
    *,
    main_module: Optional[str],
    syntax_module: Optional[str],
    backend: Optional[KompileBackend],
    output_dir: Optional[Path],
    include_dirs: Iterable[Path],
    md_selector: Optional[str],
    hook_namespaces: Iterable[str],
    emit_json,
    concrete_rules: Iterable[str],
    additional_args: Iterable[str]
) -> List[str]:
    args = []

    if main_module:
        args.extend(['--main-module', main_module])

    if syntax_module:
        args.extend(['--syntax-module', syntax_module])

    if backend:
        args += ['--backend', backend.value]

    if output_dir:
        args += ['--output-definition', str(output_dir)]

    for include_dir in include_dirs:
        args += ['-I', str(include_dir)]

    if md_selector:
        args.extend(['--md-selector', md_selector])

    if hook_namespaces:
        args.extend(['--hook-namespaces', ' '.join(hook_namespaces)])

    if emit_json:
        args.append('--emit-json')

    if concrete_rules:
        args.extend(['--concrete-rules', ','.join(concrete_rules)])

    args.extend(additional_args)

    return args


def _kompile(main_file: str, *args: str) -> CompletedProcess:
    run_args = ['kompile', main_file] + list(args)
    return run_process(run_args, _LOGGER)


def _kompiled_dir(main_file: Path, output_dir: Optional[Path] = None) -> Path:
    if output_dir:
        return output_dir

    return Path(main_file.stem + '-kompiled')
