from types import ModuleType
from typing import ClassVar

from pyk.kllvm.runtime import compile_runtime, import_runtime

from ..kompiled_test import KompiledTest


class RuntimeTest(KompiledTest):
    KOMPILE_BACKEND = 'llvm'

    runtime: ClassVar[ModuleType]

    @classmethod
    def setUpClass(cls) -> None:
        super().setUpClass()
        compile_runtime(cls.kompiled_dir)
        cls.runtime = import_runtime(cls.kompiled_dir)
