from __future__ import annotations

from typing import TYPE_CHECKING

import pyk.kllvm.load  # noqa: F401
import pyk.kllvm.load_static  # noqa: F401
from pyk.kllvm.compiler import compile_kllvm

if TYPE_CHECKING:
    from typing import Final


def test_kllvm_module() -> None:

    # Given
    kllvm_module_dir: Final = pyk.kllvm.load.KLLVM_MODULE_DIR

    # When
    kllvm_module_file = compile_kllvm(kllvm_module_dir)

    # Then
    assert pyk.kllvm.load.KLLVM_MODULE_FILE == kllvm_module_file
    assert pyk.kllvm.load.KLLVM_MODULE == pyk.kllvm.load_static.KLLVM_MODULE
