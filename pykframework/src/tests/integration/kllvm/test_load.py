from __future__ import annotations

from typing import TYPE_CHECKING

import pykframework.kllvm.load  # noqa: F401
import pykframework.kllvm.load_static  # noqa: F401
from pykframework.kllvm.compiler import compile_kllvm

if TYPE_CHECKING:
    from typing import Final


def test_kllvm_module() -> None:

    # Given
    kllvm_module_dir: Final = pykframework.kllvm.load.KLLVM_MODULE_DIR

    # When
    kllvm_module_file = compile_kllvm(kllvm_module_dir)

    # Then
    assert pykframework.kllvm.load.KLLVM_MODULE_FILE == kllvm_module_file
    assert pykframework.kllvm.load.KLLVM_MODULE == pykframework.kllvm.load_static.KLLVM_MODULE
