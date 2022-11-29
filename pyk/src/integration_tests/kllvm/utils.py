from pathlib import Path
from types import ModuleType

import pytest

from pyk.kllvm.runtime import compile_runtime, import_runtime

from ..utils import KompiledTest


class RuntimeTest(KompiledTest):
    KOMPILE_BACKEND = 'llvm'

    @pytest.fixture(scope='class')
    def runtime(self, definition_dir: Path) -> ModuleType:
        compile_runtime(definition_dir)
        return import_runtime(definition_dir)
