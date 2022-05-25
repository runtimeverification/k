from unittest import TestCase

from ..kast import KApply, KSequence, KVariable
from ..kastManip import splitConfigFrom


class TestPyk(TestCase):

    def test_splitConfigFrom(self):
        k_cell = KSequence([KApply('foo'), KApply('bar')])
        term = KApply('<k>', [k_cell])
        config, subst = splitConfigFrom(term)
        self.assertEqual(config, KApply('<k>', [KVariable('K_CELL')]))
        self.assertEqual(subst, {'K_CELL': k_cell})

        map_item_cell = KApply('<mapItem>', [KApply('foo')])
        map_cell = KApply('<mapCell>', [KApply('map_join', [map_item_cell, map_item_cell])])
        config, subst = splitConfigFrom(map_cell)
        self.assertEqual(config, KApply('<mapCell>', [KVariable('MAPCELL_CELL')]))
        self.assertEqual(subst, {'MAPCELL_CELL': KApply('map_join', [map_item_cell, map_item_cell])})
