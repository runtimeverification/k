import logging
import sys
from pathlib import Path
from types import ModuleType
from typing import Final, Type, Union

from ..cli_utils import check_dir_path, check_file_path, run_process
from .ast import Pattern
from .utils import PYTHON_EXTENSION_SUFFIX, import_from_file

_LOGGER: Final = logging.getLogger(__name__)

RUNTIME_MODULE_NAME: Final = '_kllvm_runtime'
RUNTIME_MODULE_FILE_NAME: Final = f'{RUNTIME_MODULE_NAME}{PYTHON_EXTENSION_SUFFIX}'


def compile_runtime(kompiled_dir: Union[str, Path], *, verbose: bool = False) -> Path:
    kompiled_dir = Path(kompiled_dir).resolve()
    check_dir_path(kompiled_dir)

    defn_file = kompiled_dir / 'definition.kore'
    check_file_path(defn_file)

    dt_dir = kompiled_dir / 'dt'
    check_dir_path(dt_dir)

    module_file = kompiled_dir / RUNTIME_MODULE_FILE_NAME

    args = [
        'llvm-kompile',
        str(defn_file),
        str(dt_dir),
        'python',
        '--python',
        sys.executable,
        '--',
        '-o',
        str(module_file),
    ]
    if verbose:
        args.append('-v')

    _LOGGER.info(f'Compiling python extension: {module_file.name}')
    run_process(args, logger=_LOGGER)
    return module_file


def import_runtime(kompiled_dir: Union[str, Path]) -> ModuleType:
    kompiled_dir = Path(kompiled_dir)
    check_dir_path(kompiled_dir)
    module_file = kompiled_dir / RUNTIME_MODULE_FILE_NAME
    runtime = import_from_file(RUNTIME_MODULE_NAME, module_file)
    runtime.Term = _make_term_class(runtime)  # type: ignore
    return runtime


def _make_term_class(mod: ModuleType) -> Type:
    class Term:
        def __init__(self, pattern: Pattern):
            self._block = mod.InternalTerm(pattern)

        def __str__(self) -> str:
            return str(self._block)

        def step(self, n: int = 1) -> None:
            self._block = self._block.step(n)

        def run(self) -> None:
            self.step(-1)

        def copy(self) -> 'Term':
            other = self
            other._block = self._block.step(0)
            return other

    return Term
