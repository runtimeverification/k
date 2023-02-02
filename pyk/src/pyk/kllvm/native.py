import atexit
import logging
import shutil
import sys
from pathlib import Path
from tempfile import mkdtemp
from typing import Final, Union

from ..cli_utils import check_dir_path, run_process
from .utils import PYTHON_EXTENSION_SUFFIX, import_from_file

_LOGGER: Final = logging.getLogger(__name__)

KLLVM_MODULE_NAME: Final = '_kllvm'
KLLVM_MODULE_FILE_NAME: Final = f'{KLLVM_MODULE_NAME}{PYTHON_EXTENSION_SUFFIX}'


def compile_kllvm(target_dir: Union[str, Path], *, verbose: bool = False) -> Path:
    target_dir = Path(target_dir).resolve()
    check_dir_path(target_dir)

    module_file = target_dir / KLLVM_MODULE_FILE_NAME

    args = ['llvm-kompile', 'pythonast', '--python', sys.executable, '--', '-o', str(module_file)]
    if verbose:
        args.append('-v')

    _LOGGER.info(f'Compiling pythonast extension: {module_file.name}')
    run_process(args, logger=_LOGGER)
    return module_file


KLLVM_MODULE_DIR: Final = Path(mkdtemp()).resolve(strict=True)
KLLVM_MODULE_FILE: Final = compile_kllvm(KLLVM_MODULE_DIR)
_kllvm: Final = import_from_file(KLLVM_MODULE_NAME, KLLVM_MODULE_FILE)


@atexit.register
def _cleanup() -> None:
    shutil.rmtree(KLLVM_MODULE_DIR, ignore_errors=True)
