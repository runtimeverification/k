from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from .utils import Profiler

if TYPE_CHECKING:
    from pathlib import Path


@pytest.fixture
def profile(tmp_path: Path) -> Profiler:
    return Profiler(tmp_path)
