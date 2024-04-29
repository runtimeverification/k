from __future__ import annotations

import logging
from typing import TYPE_CHECKING

from ..konvert import _ast_to_kast
from .markdown import select_code_blocks
from .outer import KDefinition
from .outer_parser import OuterParser
from .outer_syntax import Definition

if TYPE_CHECKING:
    from collections.abc import Iterable
    from pathlib import Path
    from typing import Final

    from .outer_syntax import Module

_LOGGER: Final = logging.getLogger(__name__)


def _slurp(
    definition_text: str,
    search_paths: Iterable[Path] = (),
    processed_files: list[Path] | None = None,
    md_selector: str = 'k',
) -> tuple[Module, ...]:
    processed_files = processed_files if processed_files is not None else []
    parser = OuterParser(definition_text)
    definition = parser.definition()
    result = definition.modules
    for require in definition.requires:
        try_files = [include_dir / require.path for include_dir in search_paths]
        try:
            # Get the first source file we can find by iterating through search_paths
            index = [file.exists() for file in try_files].index(True)
        except ValueError as v:
            # TODO Include the source location of the requires clause
            raise FileNotFoundError(
                f'{require.path} not found\nLookup directories: {[str(path) for path in search_paths]}'
            ) from v

        required_file = try_files[index]
        if required_file not in processed_files:
            processed_files.append(required_file)
            _LOGGER.info(f'Reading {required_file}')
            with open(required_file) as f:
                text = f.read()
                if required_file.suffix == '.md':
                    text = select_code_blocks(text, md_selector)
                result += _slurp(text, search_paths, processed_files, md_selector)
    return result


def parse_outer(
    definition_file: Path, main_module: str, search_paths: Iterable[Path] = (), md_selector: str = 'k'
) -> KDefinition:
    text = definition_file.read_text()
    if definition_file.suffix == '.md':
        text = select_code_blocks(text, md_selector)

    modules = _slurp(text, search_paths, [definition_file], md_selector)
    final_definition = _ast_to_kast(Definition(modules), main_module=main_module)
    assert isinstance(final_definition, KDefinition)
    return final_definition
