from enum import Enum
from pathlib import Path
from subprocess import CompletedProcess, run
from typing import Iterable, List, Optional

from ..cli_utils import check_dir_path, check_file_path, notif


class KompileBackend(Enum):
    LLVM = 'llvm'
    HASKELL = 'haskell'
    KORE = 'kore'
    JAVA = 'java'


def kompile(
    main_file: Path,
    *,
    backend: Optional[KompileBackend],
    output_dir: Optional[Path] = None,
    include_dirs: Iterable[Path] = (),
    emit_json=False,
) -> Path:
    check_file_path(main_file)

    for include_dir in include_dirs:
        check_dir_path(include_dir)

    args = _build_arg_list(backend=backend, output_dir=output_dir, include_dirs=include_dirs, emit_json=emit_json)

    proc_res = _kompile(str(main_file), *args)

    if proc_res.returncode:
        raise RuntimeError(f'Kompilation failed for: {main_file}')

    kompiled_dir = _kompiled_dir(main_file, output_dir)
    assert kompiled_dir.is_dir()
    return kompiled_dir


def _build_arg_list(
    *,
    backend: Optional[KompileBackend],
    output_dir: Optional[Path],
    include_dirs: Iterable[Path],
    emit_json: bool,
) -> List[str]:
    args = []

    if backend:
        args += ['--backend', backend.value]

    if output_dir:
        args += ['--output-definition', str(output_dir)]

    for include_dir in include_dirs:
        args += ['-I', str(include_dir)]

    if emit_json:
        args.append('--emit-json')

    return args


def _kompile(main_file: str, *args: str) -> CompletedProcess:
    run_args = ['kompile', main_file] + list(args)
    notif(' '.join(run_args))
    return run(run_args, capture_output=True)


def _kompiled_dir(main_file: Path, output_dir: Optional[Path] = None) -> Path:
    if output_dir:
        return output_dir

    return Path(main_file.stem + '-kompiled')
