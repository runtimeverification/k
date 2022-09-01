from unittest import TestCase

import kllvm


class KLLVMTest(TestCase):
    def test_basic(self):
        sort_int = kllvm.ast.CompositeSort('SortInt')
        self.assertEqual(str(sort_int), "SortInt{}")
