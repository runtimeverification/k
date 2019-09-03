#!/usr/bin/env python3

import sys

from functools import reduce

# From K's pyk-library
from pyk.kast      import *
from pyk.kastManip import *

IMP_symbols = { 'int_;_'       : (lambda ds, ss : 'int ' + ds + ';\n' + ss)
              , '_,_'          : assocWithUnit(' , ', '.Ids')
              , '.List{"_,_"}' : constLabel('.Ids')
              , '{}'           : constLabel('{ }')
              , '_+_'          : binOpStr('+')
              }

ALL_symbols = combineDicts(K_symbols, IMP_symbols)

kast_term = readKastTerm(sys.argv[1])

if isKRule(kast_term):
    kast_term = minimizeRule(kast_term)
    defn_name = sys.argv[1][:-5].split("/")[1]
    mod = KFlatModule(defn_name.upper(), [KImport("IMP")], [kast_term])
    kast_term = KDefinition(defn_name, [mod], requires = [KRequire("imp")])
elif isKApply(kast_term):
    kast_term = simplifyBool(kast_term)

print(prettyPrintKast(kast_term, ALL_symbols))
