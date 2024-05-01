from __future__ import annotations

import tempfile
from typing import TYPE_CHECKING

from pyk.kllvm import load

from pyk.kllvm.compiler import compile_runtime
from pyk.kllvm.convert import pattern_to_llvm
from pyk.kllvm.importer import import_runtime
from pyk.kore.prelude import top_cell_initializer, inj, SORT_K_ITEM
from pyk.kore.syntax import App, SortApp
from pyk.ktool.kompile import kompile

import sys

if TYPE_CHECKING:
    from pathlib import Path

    from pyk.kllvm.ast import Pattern


def module(name: str) -> str:
    return f"""
        module {name.upper()}
            syntax {name.title()} ::= {name}() [symbol({name})]
                         | {name}Done()
            rule {name}() => {name}Done()
        endmodule
    """


def kompile_str(mod: str, main_mod: str) -> Path:
    with tempfile.NamedTemporaryFile() as tf:
        tf.write(mod.encode('utf-8'))
        tf.flush()

        return kompile(tf.name, output_dir=f'{main_mod.lower()}-kompiled', syntax_module=main_mod, main_module=main_mod)


def start_pattern(label: str, sort: str) -> Pattern:
    kore_sort = SortApp(f'Sort{sort}')
    term = inj(kore_sort, SORT_K_ITEM, App(f'Lbl{label}'))
    return pattern_to_llvm(top_cell_initializer({'$PGM': term})).desugar_associative()

if __name__ == "__main__":
    for mod in ['foo', 'bar']:
        if mod in sys.argv:
            out_dir = kompile_str(module(mod), mod.upper())
            compile_runtime(out_dir)
            runtime = import_runtime(out_dir)
            result = runtime.run(start_pattern(mod, mod.title()))
            print(result)
