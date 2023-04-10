from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kllvm.compiler import compile_runtime
from pyk.kllvm.importer import import_runtime

from ..utils import KompiledTest

if TYPE_CHECKING:
    from pathlib import Path
    from types import ModuleType


class RuntimeTest(KompiledTest):
    KOMPILE_BACKEND = 'llvm'

    @pytest.fixture(scope='class')
    def runtime(self, definition_dir: Path) -> ModuleType:
        compile_runtime(definition_dir)
        return import_runtime(definition_dir)
