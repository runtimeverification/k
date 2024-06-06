from __future__ import annotations

import logging
import sys
import sysconfig
from pathlib import Path
from typing import TYPE_CHECKING

from ..cli.utils import check_dir_path, check_file_path
from ..utils import run_process

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Final


_LOGGER: Final = logging.getLogger(__name__)
PYTHON_EXTENSION_SUFFIX: Final = sysconfig.get_config_var('EXT_SUFFIX')


# ------
# _kllvm
# ------

KLLVM_MODULE_NAME: Final = '_kllvm'
KLLVM_MODULE_FILE_NAME: Final = f'{KLLVM_MODULE_NAME}{PYTHON_EXTENSION_SUFFIX}'


def compile_kllvm(target_dir: str | Path, *, verbose: bool = False) -> Path:
    target_dir = Path(target_dir).resolve()
    check_dir_path(target_dir)

    module_file = target_dir / KLLVM_MODULE_FILE_NAME

    args = ['llvm-kompile', 'pythonast', '--python', sys.executable, '--python-output-dir', str(target_dir)]
    if verbose:
        args += ['--verbose']

    _LOGGER.info(f'Compiling pythonast extension: {module_file.name}')
    run_process(args, logger=_LOGGER)

    assert module_file.is_file()
    return module_file


# --------------
# _kllvm_runtime
# --------------

RUNTIME_MODULE_NAME: Final = '_kllvm_runtime'
RUNTIME_MODULE_FILE_NAME: Final = f'{RUNTIME_MODULE_NAME}{PYTHON_EXTENSION_SUFFIX}'


def compile_runtime(
    definition_dir: str | Path,
    target_dir: str | Path | None = None,
    *,
    ccopts: Iterable[str] = (),
    verbose: bool = False,
) -> Path:
    definition_dir = Path(definition_dir).resolve()
    check_dir_path(definition_dir)

    if target_dir is None:
        target_dir = definition_dir
    else:
        target_dir = Path(target_dir).resolve()
        check_dir_path(target_dir)

    ccopts = list(ccopts)

    defn_file = definition_dir / 'definition.kore'
    check_file_path(defn_file)

    dt_dir = definition_dir / 'dt'
    check_dir_path(dt_dir)

    module_file = target_dir / RUNTIME_MODULE_FILE_NAME

    args = ['llvm-kompile', str(defn_file), str(dt_dir), 'python', '--python', sys.executable]
    if target_dir:
        args += ['--python-output-dir', str(target_dir)]
    if verbose:
        args += ['--verbose']
    if ccopts:
        args += ['--']
        args += ccopts

    _LOGGER.info(f'Compiling python extension: {module_file.name}')
    run_process(args, logger=_LOGGER)

    assert module_file.is_file()
    return module_file


# -------------------------------
# utility for generation of hints
# -------------------------------


def generate_hints(
    definition_dir: str | Path,
    input_kore_file: str | Path,
    target_dir: str | Path | None = None,
    hints_file_name: str = 'hints.bin',
) -> Path:
    definition_dir = Path(definition_dir).resolve()
    check_dir_path(definition_dir)

    input_kore_file = Path(input_kore_file).resolve()
    check_file_path(input_kore_file)

    if target_dir is None:
        target_dir = definition_dir
    else:
        target_dir = Path(target_dir).resolve()
        check_dir_path(target_dir)

    interpreter = definition_dir / 'interpreter'
    check_file_path(interpreter)

    hints_file = target_dir / hints_file_name

    args = [str(interpreter), str(input_kore_file), '-1', str(hints_file), '--proof-output']
    _LOGGER.info(f'Generating hints: {hints_file.name}')
    run_process(args, logger=_LOGGER)

    assert hints_file.is_file()

    return hints_file
