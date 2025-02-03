from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING, TypedDict

from .k2lean4 import K2Lean4
from .model import Module

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable

    from ..kore.internal import KoreDefn


class GenContext(TypedDict):
    package_name: str
    library_name: str


def generate(
    defn: KoreDefn,
    context: GenContext,
    *,
    output_dir: str | Path | None = None,
) -> Path:
    output_dir = Path(output_dir) if output_dir is not None else Path('.')

    k2lean4 = K2Lean4(defn)
    genmodel = {
        'Sorts': (k2lean4.sort_module, ['Prelude']),
        'Func': (k2lean4.func_module, ['Sorts']),
        'Inj': (k2lean4.inj_module, ['Sorts']),
        'Rewrite': (k2lean4.rewrite_module, ['Func', 'Inj']),
    }

    modules = _gen_modules(context['library_name'], genmodel)
    res = _gen_template(output_dir, context)
    _write_modules(res, modules)
    return res


def _gen_template(output_dir: Path, context: GenContext) -> Path:
    from cookiecutter.generate import generate_files

    template_dir = Path(__file__).parent / 'template'
    gen_res = generate_files(
        repo_dir=str(template_dir),
        output_dir=str(output_dir),
        context={'cookiecutter': context},
    )

    res = Path(gen_res)
    assert res.is_dir()
    return res


def _gen_modules(
    library_name: str,
    genmodel: dict[str, tuple[Callable[[], Module], list[str]]],
) -> dict[Path, Module]:
    def gen_module(generator: Callable[[], Module], imports: Iterable[str]) -> Module:
        imports = tuple(f'{library_name}.{importt}' for importt in imports)
        module = generator()
        module = Module(imports=imports, commands=module.commands)
        return module

    return {
        Path(library_name) / f'{name}.lean': gen_module(generator, imports)
        for name, (generator, imports) in genmodel.items()
    }


def _write_modules(output_dir: Path, modules: dict[Path, Module]) -> None:
    for path, module in modules.items():
        (output_dir / path).write_text(str(module))
