from unittest import TestCase

from pyk.utils import deconstruct_short_hash


class ShortHashTest(TestCase):
    def test_parse_short_id(self):
        # prefix with / without the dots, suffix, both prefix and suffix, full hash, etc).
        self.assertEqual(deconstruct_short_hash('..abcdef'), ('', 'abcdef'))
        self.assertEqual(deconstruct_short_hash('abcdef..'), ('abcdef', ''))
        self.assertEqual(deconstruct_short_hash('abcdef..12345'), ('abcdef', '12345'))

        full_hash = '0001000200030004000500060007000800010002000300040005000600070008'
        self.assertEqual(deconstruct_short_hash(full_hash), (full_hash, full_hash))

        # Bad short hash: Has digits between dots
        with self.assertRaises(ValueError, msg='Bad short hash: 3.c62e73544...'):
            deconstruct_short_hash('3.c62e73544...')

        # Bad short hash: Has non hex digits
        with self.assertRaises(ValueError, msg='Bad short hash: 3...XXX'):
            deconstruct_short_hash('3...XXX')

        # Bad short hash: Has more than two dots
        with self.assertRaises(ValueError, msg='Bad short hash: 3.....adf'):
            deconstruct_short_hash('3...adf')
