from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING

from ..utils import run_process_2
from .importer import import_kllvm

if TYPE_CHECKING:
    from typing import Final


def get_kllvm() -> Path:
    args = ['llvm-kompile', '--bindings-path']
    proc = run_process_2(args)
    bindings_dir = Path(proc.stdout.rstrip()).resolve()
    kllvm_dir = bindings_dir / 'kllvm'
    return kllvm_dir


KLLVM_MODULE_DIR: Final = get_kllvm()
KLLVM_MODULE: Final = import_kllvm(KLLVM_MODULE_DIR)
