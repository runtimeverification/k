from __future__ import annotations

import atexit
import shutil
from pathlib import Path
from tempfile import mkdtemp
from typing import TYPE_CHECKING

from .compiler import compile_kllvm
from .importer import import_kllvm

if TYPE_CHECKING:
    from typing import Final


KLLVM_MODULE_DIR: Final = Path(mkdtemp()).resolve(strict=True)
KLLVM_MODULE_FILE: Final = compile_kllvm(KLLVM_MODULE_DIR)
KLLVM_MODULE: Final = import_kllvm(KLLVM_MODULE_DIR)


@atexit.register
def _cleanup() -> None:
    shutil.rmtree(KLLVM_MODULE_DIR, ignore_errors=True)
