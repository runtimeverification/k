#!/usr/bin/env python3

import sys
import unittest

from functools import reduce

# From K's pyk-library
from pyk import *

class TestPyk(unittest.TestCase):

    def test_newLines(self):
        self.assertEqual(newLines(['aaa', 'bbb']), 'aaa\nbbb')
        self.assertEqual(newLines(['aaa']), 'aaa')

    def test_splitConfigFrom(self):
        k_cell = KSequence([KConstant('foo'), KConstant('bar')])
        term   = KApply('<k>', [k_cell])
        (config, subst) = splitConfigFrom(term)
        self.assertEqual(config, KApply('<k>', [KVariable('K_CELL')]))
        self.assertEqual(subst, {'K_CELL': k_cell})

        map_item_cell = KApply('<mapItem>', [KConstant('foo')])
        map_cell      = KApply('<mapCell>', [KApply('map_join', [map_item_cell, map_item_cell])])
        (config, subst) = splitConfigFrom(map_cell)
        self.assertEqual(config, KApply('<mapCell>', [KVariable('MAPCELL_CELL')]))
        self.assertEqual(subst, {'MAPCELL_CELL': KApply('map_join', [map_item_cell, map_item_cell])})

if __name__ == '__main__':
    unittest.main()
