from unittest import TestCase

from pyk.kore.parser import KoreParser
from pyk.kore.syntax import Kore

from .utils import JSON_TEST_FILES, KORE_PASS_TEST_FILES


class ParserTest(TestCase):

    def test_parse_kore(self):
        for test_file in KORE_PASS_TEST_FILES:
            with self.subTest(i=test_file.name):
                # Given
                with open(test_file, 'r') as f:
                    parser1 = KoreParser(f.read())

                # When
                definition1 = parser1.definition()
                parser2 = KoreParser(definition1.text)
                definition2 = parser2.definition()

                # Then
                self.assertTrue(parser1.eof)
                self.assertTrue(parser2.eof)
                self.assertEqual(definition1, definition2)

    def test_parse_json(self):
        for test_file in JSON_TEST_FILES:
            with self.subTest(i=test_file.name):
                # Given
                with open(test_file, 'r') as f:
                    json_text = f.read()

                # When
                kore1 = Kore.from_json(json_text)
                parser = KoreParser(kore1.text)
                kore2 = parser.pattern()
                kore3 = Kore.from_json(kore1.json)

                # Then
                self.assertTrue(parser.eof)
                self.assertEqual(kore1, kore2)
                self.assertEqual(kore1, kore3)
