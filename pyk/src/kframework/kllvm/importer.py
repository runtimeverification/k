from __future__ import annotations

import os
import sys
from contextlib import contextmanager
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from typing import TYPE_CHECKING

from ..cli.utils import check_dir_path, check_file_path
from .compiler import KLLVM_MODULE_FILE_NAME, KLLVM_MODULE_NAME, RUNTIME_MODULE_FILE_NAME, RUNTIME_MODULE_NAME
from .runtime import Runtime

if TYPE_CHECKING:
    from collections.abc import Iterator
    from types import ModuleType


@contextmanager
def rtld_local() -> Iterator[None]:
    old_flags = sys.getdlopenflags()
    sys.setdlopenflags(old_flags | os.RTLD_LOCAL)
    yield
    sys.setdlopenflags(old_flags)


def import_from_file(module_name: str, module_file: str | Path) -> ModuleType:
    module_file = Path(module_file).resolve()
    check_file_path(module_file)

    spec = spec_from_file_location(module_name, module_file)
    if not spec:
        raise ValueError('Could not create ModuleSpec')

    module = module_from_spec(spec)
    if not module:
        raise ValueError('Could not create ModuleType')

    if not spec.loader:
        raise ValueError('Spec has no loader')

    spec.loader.exec_module(module)

    return module


def import_kllvm(target_dir: str | Path) -> ModuleType:
    if '_kllvm' in sys.modules:
        return sys.modules['_kllvm']
    target_dir = Path(target_dir)
    check_dir_path(target_dir)
    module_file = target_dir / KLLVM_MODULE_FILE_NAME
    return import_from_file(KLLVM_MODULE_NAME, module_file)


def import_runtime(target_dir: str | Path) -> Runtime:
    target_dir = Path(target_dir)
    check_dir_path(target_dir)
    module_file = target_dir / RUNTIME_MODULE_FILE_NAME

    with rtld_local():
        module = import_from_file(RUNTIME_MODULE_NAME, module_file)

    return Runtime(module)
