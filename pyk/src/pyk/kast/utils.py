from __future__ import annotations

import logging
from pathlib import Path
from typing import TYPE_CHECKING

from ._ast_to_kast import _ast_to_kast
from .markdown import select_code_blocks
from .outer import KDefinition
from .outer_parser import OuterParser
from .outer_syntax import Definition

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Final

    from .outer_syntax import Require

_LOGGER: Final = logging.getLogger(__name__)


def parse_outer(
    definition_file: str | Path,
    main_module: str,
    *,
    include_dirs: Iterable[str | Path] = (),
    md_selector: str = 'k',
    include_source: bool = True,
) -> KDefinition:
    parsed_files = slurp_definitions(
        definition_file,
        include_dirs=include_dirs,
        md_selector=md_selector,
        include_source=include_source,
    )
    modules = tuple(module for _, definition in parsed_files.items() for module in definition.modules)
    final_definition = _ast_to_kast(Definition(modules), main_module=main_module)
    assert isinstance(final_definition, KDefinition)
    return final_definition


def slurp_definitions(
    main_file: str | Path,
    *,
    include_dirs: Iterable[str | Path] = (),
    md_selector: str | None = None,
    include_source: bool = True,
) -> dict[Path, Definition]:
    main_file = Path(main_file).resolve()
    _include_dirs = [Path(include_dir) for include_dir in include_dirs]
    md_selector = md_selector or 'k'

    result: dict[Path, Definition] = {}

    pending = [main_file]
    while pending:  # DFS
        current_file = pending.pop()

        if current_file in result:
            continue

        definition = _parse_file(current_file, md_selector, include_source)
        pending += reversed([_resolve_require(require, current_file, _include_dirs) for require in definition.requires])

        result[current_file] = definition

    return result


def _parse_file(definition_file: Path, md_selector: str, include_source: bool) -> Definition:
    _LOGGER.info(f'Reading {definition_file}')

    text = definition_file.read_text()
    if definition_file.suffix == '.md':
        text = select_code_blocks(text, md_selector)

    parser = OuterParser(text, source=definition_file if include_source else None)
    return parser.definition()


def _resolve_require(require: Require, definition_file: Path, include_dirs: list[Path]) -> Path:
    try_dirs = [definition_file.parent] + include_dirs
    try_files = [try_dir / require.path for try_dir in try_dirs]
    for file in try_files:
        if file.is_file():
            return file.resolve()
    raise FileNotFoundError(f'{require.path} not found. Searched paths: {[str(path) for path in try_dirs]}')
