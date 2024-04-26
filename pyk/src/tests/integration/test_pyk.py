from __future__ import annotations

import json
import sys
from typing import TYPE_CHECKING

import pytest

from pyk.__main__ import main
from pyk.testing import KompiledTest

from .utils import K_FILES, TEST_DATA_DIR

if TYPE_CHECKING:
    from collections.abc import Iterable
    from pathlib import Path

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
    KOMPILE_MAIN_FILE = K_FILES / 'd.k'
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
    KOMPILE_MAIN_FILE = K_FILES / 'imp-verification.k'
    KOMPILE_BACKEND = 'haskell'

    def test_minimize_term(self, assume_argv: AssumeArgv, tmp_path: Path, definition_dir: Path) -> None:
        expected_file = K_FILES / 'imp-unproveable-spec.k.expected'
        prove_res_file = tmp_path / 'term.json'
        actual_file = tmp_path / 'imp-unproveable-spec.k.out'

        assume_argv(
            [
                'pyk',
                'prove-legacy',
                str(definition_dir),
                str(K_FILES / 'imp-verification.k'),
                str(K_FILES / 'imp-unproveable-spec.k'),
                'IMP-UNPROVEABLE-SPEC',
                '--output-file',
                str(prove_res_file),
            ]
        )
        main()
        assume_argv(['pyk', 'print', str(definition_dir), str(prove_res_file), '--output-file', str(actual_file)])
        main()
        # assert expected_file.read_text() == actual_file.read_text()
        expected_file.write_text(actual_file.read_text())


class TestRpcPrint(KompiledTest):
    KOMPILE_MAIN_FILE = K_FILES / 'imp.k'
    KOMPILE_BACKEND = 'haskell'

    TEST_DATA = [
        'imp-execute-request',
        'imp-execute-depth-bound-response',
        'imp-execute-terminal-rule-response',
        'imp-execute-cut-point-rule-response',
        'imp-execute-branching-response',
        'imp-execute-stuck-response',
        'imp-simplify-request',
        'imp-simplify-response',
    ]
    TEST_DATA_FAILING = ['non-exisiting-file']

    @pytest.mark.parametrize('filename_stem', TEST_DATA, ids=TEST_DATA)
    def test_rpc_print(self, assume_argv: AssumeArgv, tmp_path: Path, definition_dir: Path, filename_stem: str) -> None:
        # Given
        input_file = TEST_DATA_DIR / 'pyk-rpc-print' / f'{filename_stem}.json'
        expected_file = TEST_DATA_DIR / 'pyk-rpc-print' / f'{filename_stem}.pretty.golden'
        actual_file = tmp_path / f'{filename_stem}.pretty'
        assume_argv(['pyk', 'rpc-print', str(definition_dir), str(input_file), '--output-file', str(actual_file)])

        # When
        main()

        # Then
        expected_lines = {line.strip() for line in expected_file.read_text().splitlines()}
        actual_lines = {line.strip() for line in actual_file.read_text().splitlines()}
        assert actual_lines == expected_lines

    @pytest.mark.parametrize('filename_stem', TEST_DATA_FAILING, ids=TEST_DATA_FAILING)
    def test_rpc_print_fail(
        self, assume_argv: AssumeArgv, tmp_path: Path, definition_dir: Path, filename_stem: str
    ) -> None:
        # Given
        input_file = TEST_DATA_DIR / 'pyk-rpc-print' / f'{filename_stem}.json'
        actual_file = tmp_path / f'{filename_stem}.pretty'
        assume_argv(['pyk', 'rpc-print', str(definition_dir), str(input_file), '--output-file', str(actual_file)])

        # When
        with pytest.raises(SystemExit):
            main()


class TestRpcKast:
    TEST_DATA = [
        ('imp-execute-request', 'imp-execute-depth-bound-response', 'imp-execute-request-from-execute-response'),
        ('imp-simplify-request', 'imp-execute-depth-bound-response', 'imp-simplify-request-from-execute-response'),
    ]

    @pytest.mark.parametrize(
        'reference_filename_stem, input_filename_stem, output_filename_stem',
        TEST_DATA,
        ids=[id for id, _ in enumerate(TEST_DATA)],
    )
    def test_rpc_kast(
        self,
        assume_argv: AssumeArgv,
        tmp_path: Path,
        reference_filename_stem: str,
        input_filename_stem: str,
        output_filename_stem: str,
    ) -> None:
        # Given
        reference_file = TEST_DATA_DIR / 'pyk-rpc-kast' / f'{reference_filename_stem}.json'
        input_file = TEST_DATA_DIR / 'pyk-rpc-kast' / f'{input_filename_stem}.json'
        expected_file = TEST_DATA_DIR / 'pyk-rpc-kast' / f'{output_filename_stem}.json.golden'
        actual_file = tmp_path / f'{output_filename_stem}.json'
        assume_argv(
            [
                'pyk',
                'rpc-kast',
                str(reference_file),
                str(input_file),
                '--output-file',
                str(actual_file),
            ]
        )

        # When
        main()

        # Then
        expected = json.loads(expected_file.read_text())
        actual = json.loads(actual_file.read_text())
        assert actual == expected
