from __future__ import annotations

from pathlib import Path

from pyk.kore.rpc import BoosterServer, KoreExecLogFormat, KoreServer


def _make_kore_server(
    log_axioms_file: Path | None,
    haskell_log_format: KoreExecLogFormat = KoreExecLogFormat.JSON,
    haskell_log_entries: list[str] | None = None,
) -> KoreServer:
    server = object.__new__(KoreServer)
    server._log_axioms_file = log_axioms_file  # type: ignore[attr-defined]
    server._haskell_log_format = haskell_log_format  # type: ignore[attr-defined]
    server._haskell_log_entries = list(haskell_log_entries or [])  # type: ignore[attr-defined]
    return server


def _make_booster_server(
    log_axioms_file: Path | None,
    haskell_log_format: KoreExecLogFormat = KoreExecLogFormat.JSON,
    haskell_log_entries: list[str] | None = None,
) -> BoosterServer:
    server = object.__new__(BoosterServer)
    server._log_axioms_file = log_axioms_file  # type: ignore[attr-defined]
    server._haskell_log_format = haskell_log_format  # type: ignore[attr-defined]
    server._haskell_log_entries = list(haskell_log_entries or [])  # type: ignore[attr-defined]
    return server


class TestKoreServerHaskellLogCliArgs:
    def test_no_log_file_emits_no_args(self) -> None:
        server = _make_kore_server(log_axioms_file=None, haskell_log_entries=['Simplify'])
        assert server._haskell_log_cli_args() == []

    def test_emits_kore_rpc_style_flags(self) -> None:
        server = _make_kore_server(
            log_axioms_file=Path('/tmp/kore.jsonl'),
            haskell_log_format=KoreExecLogFormat.JSON,
            haskell_log_entries=['KoreCalls', 'Simplify', 'Aborts'],
        )
        # kore-rpc accepts `--log FILE` and `--log-entries A,B,C`.
        assert server._haskell_log_cli_args() == [
            '--log',
            '/tmp/kore.jsonl',
            '--log-format',
            'json',
            '--log-entries',
            'KoreCalls,Simplify,Aborts',
        ]


class TestBoosterServerHaskellLogCliArgs:
    def test_no_log_file_emits_no_args(self) -> None:
        server = _make_booster_server(log_axioms_file=None, haskell_log_entries=['Simplify'])
        assert server._haskell_log_cli_args() == []

    def test_emits_booster_style_flags(self) -> None:
        server = _make_booster_server(
            log_axioms_file=Path('/tmp/kore.jsonl'),
            haskell_log_format=KoreExecLogFormat.JSON,
            haskell_log_entries=['KoreCalls', 'Simplify', 'Aborts'],
        )
        # kore-rpc-booster requires `--log-file FILE` and one `-l ENTRY` per entry.
        assert server._haskell_log_cli_args() == [
            '--log-file',
            '/tmp/kore.jsonl',
            '--log-format',
            'json',
            '-l',
            'KoreCalls',
            '-l',
            'Simplify',
            '-l',
            'Aborts',
        ]

    def test_emits_log_file_with_no_entries(self) -> None:
        server = _make_booster_server(
            log_axioms_file=Path('/tmp/kore.jsonl'),
            haskell_log_format=KoreExecLogFormat.ONELINE,
            haskell_log_entries=[],
        )
        assert server._haskell_log_cli_args() == [
            '--log-file',
            '/tmp/kore.jsonl',
            '--log-format',
            'oneline',
        ]
