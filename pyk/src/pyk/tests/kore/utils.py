from pathlib import Path
from typing import Final

# JSON files for random generated patterns
_JSON_TEST_DIR: Final = Path(__file__).parent / 'json_data'

JSON_TEST_FILES: Final = tuple(_JSON_TEST_DIR.iterdir())

# Haskell backend Kore test files containing definitions
_KORE_TEST_DIR: Final = Path(__file__).parents[5] / 'haskell-backend/src/main/native/haskell-backend/test/parser'
_KORE_TEST_INPUT: Final = tuple(
    (test_file, test_file.with_suffix('.kore.golden'))
    for test_file in _KORE_TEST_DIR.iterdir()
    if test_file.suffix == '.kore'
)

KORE_PASS_TEST_FILES: Final = tuple(
    test_file for test_file, golden_file in _KORE_TEST_INPUT if golden_file.stat().st_size == 0
)
KORE_FAIL_TEST_FILES: Final = tuple(
    test_file for test_file, golden_file in _KORE_TEST_INPUT if golden_file.stat().st_size > 0
)
