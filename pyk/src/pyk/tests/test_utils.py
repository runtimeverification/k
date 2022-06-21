from unittest import TestCase

from ..utils import deconstruct_short_hash


class KCFGTestCase(TestCase):
    def test_parse_short_id(self):
        # Bad short hash: Has digits between dots
        with self.assertRaisesRegex(ValueError, 'Bad short hash: 3\\.c62e73544\\.\\.\\.'):
            deconstruct_short_hash('3.c62e73544...')

        # Bad short hash: Has non hex digits
        with self.assertRaisesRegex(ValueError, 'Bad short hash: 3\\.\\.\\.XXX'):
            deconstruct_short_hash('3...XXX')

        # Bad short hash: Has more than three dots
        with self.assertRaisesRegex(ValueError, 'Bad short hash: 3\\.\\.\\.\\.\\.adf'):
            deconstruct_short_hash('3.....adf')
