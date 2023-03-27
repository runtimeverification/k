from pathlib import Path

import pytest

from .utils import Profiler


@pytest.fixture
def profile(tmp_path: Path) -> Profiler:
    return Profiler(tmp_path)
