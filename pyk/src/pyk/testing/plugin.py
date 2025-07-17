from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING

import pytest

from ..utils import BugReport, ensure_dir_path
from ._kompiler import Kompiler, UseServer
from ._profiler import Profiler

if TYPE_CHECKING:
    from pytest import FixtureRequest, Parser, TempPathFactory


def pytest_addoption(parser: Parser) -> None:
    parser.addoption(
        '--bug-report',
        action='store_true',
        default=False,
        help='Generate bug reports',
    )
    parser.addoption(
        '--bug-report-dir',
        type=ensure_dir_path,
        help='Directory to store bug reports',
    )
    parser.addoption(
        '--use-server',
        type=UseServer,
        default=UseServer.BOTH,
        help='KORE RPC server to use for tests',
    )


@pytest.fixture
def bug_report(request: FixtureRequest, tmp_path: Path) -> BugReport | None:
    bug_report = request.config.getoption('--bug-report')
    if not bug_report:
        return None
    bug_report_dir = request.config.getoption('--bug-report-dir')
    if not bug_report_dir:
        bug_report_dir = tmp_path
    br_name = request.node.name.replace('[', '/')
    br_path = Path(bug_report_dir / br_name)
    ensure_dir_path(br_path.parent)
    return BugReport(br_path)


@pytest.fixture(scope='session')
def use_server(request: FixtureRequest) -> UseServer:
    return request.config.getoption('--use-server')


@pytest.fixture
def profile(tmp_path: Path) -> Profiler:
    return Profiler(tmp_path)


@pytest.fixture(scope='session')
def kompile(tmp_path_factory: TempPathFactory) -> Kompiler:
    return Kompiler(tmp_path_factory)


@pytest.fixture(scope='session')
def load_kllvm(tmp_path_factory: TempPathFactory) -> None:
    """Generate and import the ``_kllvm`` bindings module.

    Use this fixture in all tests that import from ``pyk.kllvm``.
    It ensures transitive imports of ``_kllvm`` are successful.

    Example:
        .. code-block:: python

            def test_symbol_name(load_kllvm: None) -> None:
                from pyk.kllvm.ast import Symbol

                name = "Lbl'UndsPlus'Int'Unds'"
                symbol = Symbol(name)
                assert symbol.name == name
    """
    from ..kllvm.compiler import compile_kllvm
    from ..kllvm.importer import import_kllvm

    tmp_dir = tmp_path_factory.mktemp('kllvm')
    module_file = compile_kllvm(tmp_dir)
    import_kllvm(module_file)
