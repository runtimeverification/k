from pathlib import Path
from typing import Final, Tuple
from unittest import TestCase

from pyk.kore.parser import KoreParser
from pyk.kore.syntax import Kore


class ParserTest(TestCase):
    TEST_DATA_DIR: Final[Path] = Path(__file__).parent / 'json_data'
    TEST_FILES: Final[Tuple[Path, ...]] = tuple(TEST_DATA_DIR.iterdir())

    def test_parse_pattern(self):
        for test_file in self.TEST_FILES:
            with self.subTest(i=test_file.name):
                with open(test_file, 'r') as f:
                    # When
                    kore1 = Kore.from_json(f.read())
                    parser = KoreParser(kore1.text)
                    kore2 = parser.pattern()

                    # Then
                    self.assertTrue(parser.eof)
                    self.assertEqual(kore1, kore2)
