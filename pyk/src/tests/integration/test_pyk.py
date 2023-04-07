from __future__ import annotations

import sys
from pathlib import Path
from typing import TYPE_CHECKING

import pytest

from pyk.__main__ import main

from .utils import KompiledTest

if TYPE_CHECKING:
    from collections.abc import Iterable

    from pytest import MonkeyPatch


class AssumeArgv:
    _monkeypatch: MonkeyPatch

    def __init__(self, monkeypatch: MonkeyPatch):
        self._monkeypatch = monkeypatch

    def __call__(self, argv: Iterable[str]) -> None:
        self._monkeypatch.setattr(sys, 'argv', list(argv))


@pytest.fixture
def assume_argv(monkeypatch: MonkeyPatch) -> AssumeArgv:
    return AssumeArgv(monkeypatch)


class TestGraphImports(KompiledTest):
    KOMPILE_MAIN_FILE = 'k-files/d.k'
    KOMPILE_BACKEND = 'haskell'

    def test_graph_imports(self, assume_argv: AssumeArgv, definition_dir: Path) -> None:
        # Given
        expected_file = definition_dir / 'import-graph'
        expected_lines = {
            'A',
            'A -> "A-SYNTAX"',
            '"A-SYNTAX"',
            'B',
            'B -> A',
            'B -> "B-SYNTAX"',
            '"B-SYNTAX"',
            'C',
            'C -> A',
            'C -> "C-SYNTAX"',
            '"C-SYNTAX"',
            'D',
            'D -> B',
            'D -> C',
            'D -> "D-SYNTAX"',
            '"D-SYNTAX"',
        }
        assume_argv(['pyk', 'graph-imports', str(definition_dir)])

        # When
        main()

        # Then
        assert expected_file.is_file()
        actual_lines = {line.strip() for line in expected_file.read_text().splitlines()}
        missed_lines = expected_lines - actual_lines
        assert not missed_lines


class TestMinimizeTerm(KompiledTest):
    KOMPILE_MAIN_FILE = 'k-files/imp-verification.k'
    KOMPILE_BACKEND = 'haskell'

    def test_minimize_term(self, assume_argv: AssumeArgv, tmp_path: Path, definition_dir: Path) -> None:
        expected_file = Path('k-files/imp-unproveable-spec.k.expected')
        prove_res_file = tmp_path / 'term.json'
        actual_file = tmp_path / 'imp-unproveable-spec.k.out'

        assume_argv(
            [
                'pyk',
                'prove',
                str(definition_dir),
                'k-files/imp-verification.k',
                'k-files/imp-unproveable-spec.k',
                'IMP-UNPROVEABLE-SPEC',
                '--output-file',
                str(prove_res_file),
            ]
        )
        main()
        assume_argv(['pyk', 'print', str(definition_dir), str(prove_res_file), '--output-file', str(actual_file)])
        main()
        assert expected_file.read_text() == actual_file.read_text()
