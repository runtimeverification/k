#!/usr/bin/env python3

import sys

from functools import reduce

# From K's pyk-library
from util import *
from kast import *
from pyk  import *

IMP_symbols = { 'int_;_'       : (lambda ds, ss : 'int ' + ds + ';\n' + ss)
              , '_,_'          : assocWithUnit(' , ', '.Ids')
              , '.List{"_,_"}' : constLabel('.Ids')
              , '{}'           : constLabel('{ }')
              }

ALL_symbols = combineDicts(K_symbols, IMP_symbols)

kast_term = readKastTerm(sys.argv[1])
print(prettyPrintKast(kast_term, ALL_symbols))
