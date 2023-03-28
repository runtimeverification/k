from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from .utils import Kompiler

if TYPE_CHECKING:
    from pytest import TempPathFactory


@pytest.fixture(scope='session')
def kompile(tmp_path_factory: TempPathFactory) -> Kompiler:
    return Kompiler(tmp_path_factory)
