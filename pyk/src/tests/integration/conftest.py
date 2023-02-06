import pytest
from pytest import TempPathFactory

from .utils import Kompiler


@pytest.fixture(scope='session')
def kompile(tmp_path_factory: TempPathFactory) -> Kompiler:
    return Kompiler(tmp_path_factory)
