from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING

import pytest

from pyk.kore.rpc import BoosterServer, KoreExecLogFormat, KoreServer

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Final


def _server(
    server_cls: type[KoreServer],
    log_axioms_file: Path | None,
    haskell_log_format: KoreExecLogFormat,
    haskell_log_entries: Iterable[str],
) -> KoreServer:
    # Bypass __init__ (which would start a real server) to exercise the pure CLI-arg builder.
    server = object.__new__(server_cls)
    server._log_axioms_file = log_axioms_file  # type: ignore[attr-defined]
    server._haskell_log_format = haskell_log_format  # type: ignore[attr-defined]
    server._haskell_log_entries = list(haskell_log_entries)  # type: ignore[attr-defined]
    return server


_JSON: Final = KoreExecLogFormat.JSON
_LOG_FILE: Final = Path('/tmp/kore.jsonl')

HASKELL_LOG_CLI_ARGS_TEST_DATA: Final[
    tuple[tuple[str, type[KoreServer], Path | None, KoreExecLogFormat, list[str], list[str]], ...]
] = (
    # KoreServer emits the kore-rpc form: `--log FILE`, `--log-entries A,B,C`.
    ('kore-no-log-file', KoreServer, None, _JSON, ['Simplify'], []),
    (
        'kore-flags',
        KoreServer,
        _LOG_FILE,
        _JSON,
        ['KoreCalls', 'Simplify', 'Aborts'],
        ['--log', '/tmp/kore.jsonl', '--log-format', 'json', '--log-entries', 'KoreCalls,Simplify,Aborts'],
    ),
    # BoosterServer emits the booster form: `--log-file FILE` and one `-l ENTRY` per entry.
    ('booster-no-log-file', BoosterServer, None, _JSON, ['Simplify'], []),
    (
        'booster-flags',
        BoosterServer,
        _LOG_FILE,
        _JSON,
        ['KoreCalls', 'Simplify', 'Aborts'],
        ['--log-file', '/tmp/kore.jsonl', '--log-format', 'json', '-l', 'KoreCalls', '-l', 'Simplify', '-l', 'Aborts'],
    ),
    (
        'booster-no-entries',
        BoosterServer,
        _LOG_FILE,
        KoreExecLogFormat.ONELINE,
        [],
        ['--log-file', '/tmp/kore.jsonl', '--log-format', 'oneline'],
    ),
)


@pytest.mark.parametrize(
    'test_id,server_cls,log_axioms_file,haskell_log_format,haskell_log_entries,expected',
    HASKELL_LOG_CLI_ARGS_TEST_DATA,
    ids=[test_id for test_id, *_ in HASKELL_LOG_CLI_ARGS_TEST_DATA],
)
def test_haskell_log_cli_args(
    test_id: str,
    server_cls: type[KoreServer],
    log_axioms_file: Path | None,
    haskell_log_format: KoreExecLogFormat,
    haskell_log_entries: list[str],
    expected: list[str],
) -> None:
    server = _server(server_cls, log_axioms_file, haskell_log_format, haskell_log_entries)
    assert server._haskell_log_cli_args() == expected
