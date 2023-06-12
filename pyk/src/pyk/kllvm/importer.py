from __future__ import annotations

from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from typing import TYPE_CHECKING

from ..cli.utils import check_dir_path, check_file_path
from .compiler import KLLVM_MODULE_FILE_NAME, KLLVM_MODULE_NAME, RUNTIME_MODULE_FILE_NAME, RUNTIME_MODULE_NAME

if TYPE_CHECKING:
    from collections.abc import Callable
    from types import ModuleType

    from .ast import Pattern


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
    target_dir = Path(target_dir)
    check_dir_path(target_dir)
    module_file = target_dir / KLLVM_MODULE_FILE_NAME
    return import_from_file(KLLVM_MODULE_NAME, module_file)


def import_runtime(target_dir: str | Path) -> ModuleType:
    target_dir = Path(target_dir)
    check_dir_path(target_dir)
    module_file = target_dir / RUNTIME_MODULE_FILE_NAME
    runtime = import_from_file(RUNTIME_MODULE_NAME, module_file)
    _patch_runtime(runtime)
    return runtime


def _patch_runtime(runtime: ModuleType) -> None:
    runtime.Term = _make_term_class(runtime)  # type: ignore
    runtime.interpret = _make_interpreter(runtime)  # type: ignore


def _make_interpreter(runtime: ModuleType) -> Callable[..., Pattern]:
    def interpret(pattern: Pattern, *, depth: int | None = None) -> Pattern:
        init_term = runtime.InternalTerm(pattern)
        final_term = init_term.step(depth if depth is not None else -1)
        return final_term.to_pattern()

    return interpret


def _make_term_class(mod: ModuleType) -> type:
    class Term:
        def __init__(self, pattern: Pattern):
            self._block = mod.InternalTerm(pattern)

        @property
        def pattern(self) -> Pattern:
            return self._block.to_pattern()

        @staticmethod
        def deserialize(bs: bytes) -> Term | None:
            block = mod.InternalTerm.deserialize(bs)
            if block is None:
                return None
            term = object.__new__(Term)
            term._block = block
            return term

        def serialize(self) -> bytes:
            return self._block.serialize()

        def step(self, n: int = 1) -> None:
            self._block = self._block.step(n)

        def run(self) -> None:
            self.step(-1)

        def copy(self) -> Term:
            other = self
            other._block = self._block.step(0)
            return other

        def __str__(self) -> str:
            return str(self._block)

    return Term
