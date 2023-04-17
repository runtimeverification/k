from __future__ import annotations

import logging
import sys
import sysconfig
from pathlib import Path
from typing import TYPE_CHECKING

from ..cli_utils import check_dir_path, check_file_path, run_process

if TYPE_CHECKING:
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

    assert module_file.exists()
    return module_file


# --------------
# _kllvm_runtime
# --------------

RUNTIME_MODULE_NAME: Final = '_kllvm_runtime'
RUNTIME_MODULE_FILE_NAME: Final = f'{RUNTIME_MODULE_NAME}{PYTHON_EXTENSION_SUFFIX}'


def compile_runtime(definition_dir: str | Path, target_dir: str | Path | None = None, *, verbose: bool = False) -> Path:
    definition_dir = Path(definition_dir).resolve()
    check_dir_path(definition_dir)

    if target_dir is not None:
        target_dir = Path(target_dir).resolve()
        check_dir_path(target_dir)

    defn_file = definition_dir / 'definition.kore'
    check_file_path(defn_file)

    dt_dir = definition_dir / 'dt'
    check_dir_path(dt_dir)

    module_file = definition_dir / RUNTIME_MODULE_FILE_NAME

    args = ['llvm-kompile', str(defn_file), str(dt_dir), 'python', '--python', sys.executable]
    if target_dir:
        args += ['--python-output-dir', str(target_dir)]
    if verbose:
        args += ['--verbose']

    _LOGGER.info(f'Compiling python extension: {module_file.name}')
    run_process(args, logger=_LOGGER)

    assert module_file.exists()
    return module_file
