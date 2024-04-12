from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kore.kompiled import KompiledKore
from pyk.testing import KompiledTest

from ..utils import K_FILES

if TYPE_CHECKING:
    from pathlib import Path


class TestKompiledKore(KompiledTest):
    KOMPILE_MAIN_FILE = K_FILES / 'imp.k'
    KOMPILE_BACKEND = 'haskell'

    @pytest.fixture
    def kompiled_kore(self, definition_dir: Path) -> KompiledKore:
        return KompiledKore.load(definition_dir)

    def test_to_dict(self, kompiled_kore: KompiledKore) -> None:
        # When
        dct = kompiled_kore.to_dict()
        actual = KompiledKore.from_dict(dct)

        # Then
        assert actual == kompiled_kore
