#!/usr/bin/env python3

import sys

from functools import reduce

# From K's pyk-library
from pyk import *

IMP_definition = readKastTerm('imp-kompiled/compiled.json')

IMP_symbols = buildSymbolTable(IMP_definition)

IMP_symbols['_,_']          = assocWithUnit(' , ', '')
IMP_symbols['.List{"_,_"}'] = constLabel('')

kast_term = readKastTerm(sys.argv[1])

if isKRule(kast_term):
    kast_term = minimizeRule(kast_term)
    defn_name = sys.argv[1][:-5].split("/")[1]
    mod = KFlatModule(defn_name.upper(), ["IMP"], [kast_term])
    kast_term = KDefinition(defn_name, [mod], requires = [KRequire("imp")])
elif isKApply(kast_term):
    kast_term = simplifyBool(kast_term)

print(prettyPrintKast(kast_term, IMP_symbols))
