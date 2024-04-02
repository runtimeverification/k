from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from typing import Final

TEST_DATA_DIR: Final = Path(__file__).parent / 'test-data'
K_FILES: Final = TEST_DATA_DIR / 'k-files'
