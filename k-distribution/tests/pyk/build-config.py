#!/usr/bin/env python3

import sys

from functools import reduce

# From K's pyk-library
from util import *
from kast import *
from pyk  import *

IMP_symbols = { 'int_;__IMP-SYNTAX'       : (lambda ds, ss : 'int ' + ds + ';\n' + ss)
              , '_,__IMP-SYNTAX'          : assocWithUnit(' , ', '.Ids')
              , '.List{"_,__IMP-SYNTAX"}' : constLabel('.Ids')
              , '{}_IMP-SYNTAX'           : constLabel('{ }')
              }

ALL_symbols = combineDicts(K_symbols, IMP_symbols)

def declareVars(vList):
    argTokens   = [KToken(v, 'Id') for v in vList]
    asIdList    = lambda rest, v: KApply('_,__IMP-SYNTAX', [v, rest])
    emptyIdList = KApply('.List{"_,__IMP-SYNTAX"}', [])
    return reduce(asIdList, reversed(argTokens), emptyIdList)

symbolic_configuration = KApply ( '<T>' , [ KApply ( '<k>'     , [ KVariable('K_CELL')     ] )
                                          , KApply ( '<state>' , [ KVariable('STATE_CELL') ] )
                                          ]
                                )

init_cells = { 'K_CELL'     : KApply('int_;__IMP-SYNTAX', [declareVars(['x', 'y']), KApply('{}_IMP-SYNTAX', [])])
             , 'STATE_CELL' : KApply('.Map', [])
             }

instantiated_configuration = substitute(symbolic_configuration, init_cells)

print(prettyPrintKast(instantiated_configuration, ALL_symbols))
