from __future__ import annotations

import logging
from typing import TYPE_CHECKING

from ._ast_to_kast import _ast_to_kast
from .markdown import select_code_blocks
from .outer import KDefinition
from .outer_parser import OuterParser
from .outer_syntax import Definition

if TYPE_CHECKING:
    from collections.abc import Iterable
    from pathlib import Path
    from typing import Final

    from .outer_syntax import Module, Require

_LOGGER: Final = logging.getLogger(__name__)


def parse_outer(
    definition_file: Path,
    main_module: str,
    *,
    search_paths: Iterable[Path] = (),
    md_selector: str = 'k',
    include_source: bool = True,
) -> KDefinition:
    modules = _slurp(
        definition_file,
        search_paths=search_paths,
        processed_files=[definition_file],
        md_selector=md_selector,
        include_source=include_source,
    )
    final_definition = _ast_to_kast(Definition(modules), main_module=main_module)
    assert isinstance(final_definition, KDefinition)
    return final_definition


def _slurp(
    definition_file: Path,
    *,
    search_paths: Iterable[Path] = (),
    processed_files: list[Path] | None = None,
    md_selector: str = 'k',
    include_source: bool = True,
) -> tuple[Module, ...]:
    processed_files = processed_files if processed_files is not None else []
    _LOGGER.info(f'Reading {definition_file}')
    text = definition_file.read_text()
    if definition_file.suffix == '.md':
        text = select_code_blocks(text, md_selector)
    parser = OuterParser(text, source=definition_file if include_source else None)
    definition = parser.definition()
    result = definition.modules
    for require in definition.requires:
        required_file = _resolve_require(require, search_paths)
        if required_file not in processed_files:
            processed_files.append(required_file)
            result += _slurp(
                required_file,
                search_paths=search_paths,
                processed_files=processed_files,
                md_selector=md_selector,
                include_source=include_source,
            )
    return result


def _resolve_require(require: Require, search_paths: Iterable[Path]) -> Path:
    try_files = [include_dir / require.path for include_dir in search_paths]
    for file in try_files:
        if file.is_file():
            return file.resolve()
    raise FileNotFoundError(f'{require.path} not found. Search paths: {[str(path) for path in search_paths]}')
