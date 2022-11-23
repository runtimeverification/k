from pathlib import Path
from typing import Final

from ..cli_utils import run_process
from .utils import PYTHON_EXTENSION_SUFFIX, import_from_file

KLLVM_MODULE_NAME: Final = '_kllvm'
KLLVM_MODULE_FILE_NAME: Final = f'{KLLVM_MODULE_NAME}{PYTHON_EXTENSION_SUFFIX}'
KLLVM_BINDINGS_PATH = Path(run_process(['llvm-kompile', '--bindings-path'], pipe_stderr=True).stdout.strip())
KLLVM_MODULE_DIR: Final = (KLLVM_BINDINGS_PATH / 'kllvm').resolve(strict=True)
KLLVM_MODULE_FILE: Final = (KLLVM_MODULE_DIR / KLLVM_MODULE_FILE_NAME).resolve(strict=True)
_kllvm: Final = import_from_file(KLLVM_MODULE_NAME, KLLVM_MODULE_FILE)
