from pathlib import Path
from typing import Final, Tuple
from unittest import TestCase

from pyk.kore.syntax import Kore


# TODO extend test input with field for textual Kore for comparing parse results
class FromJsonTest(TestCase):
    TEST_DATA_DIR: Final[Path] = Path(__file__).parent / 'from_json_data'
    TEST_FILES: Final[Tuple[Path, ...]] = tuple(TEST_DATA_DIR.iterdir())

    def test_from_json(self):
        for test_file in self.TEST_FILES:
            with self.subTest(i=test_file.name):
                with open(test_file, 'r') as f:
                    # When
                    kore = Kore.from_json(f.read())

                    # Then
                    self.assertIsNotNone(kore)
