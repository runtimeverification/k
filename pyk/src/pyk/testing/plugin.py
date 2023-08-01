from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from ..utils import BugReport
from ._kompiler import Kompiler
from ._profiler import Profiler

if TYPE_CHECKING:
    from pathlib import Path

    from pytest import FixtureRequest, Parser, TempPathFactory


def pytest_addoption(parser: Parser) -> None:
    parser.addoption(
        '--bug-report',
        action='store_true',
        default=False,
        help='Generate bug reports',
    )


@pytest.fixture
def bug_report(request: FixtureRequest, tmp_path: Path) -> BugReport | None:
    bug_report = request.config.getoption('--bug-report')
    return BugReport(tmp_path / 'bug-report') if bug_report else None


@pytest.fixture
def profile(tmp_path: Path) -> Profiler:
    return Profiler(tmp_path)


@pytest.fixture(scope='session')
def kompile(tmp_path_factory: TempPathFactory) -> Kompiler:
    return Kompiler(tmp_path_factory)
