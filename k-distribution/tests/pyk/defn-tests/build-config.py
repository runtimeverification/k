#!/usr/bin/env python3

import sys

from functools import reduce

# From K's pyk-library
from pyk import *

definition = sys.argv[1]
IMP_definition = readKastTerm(definition)

IMP_symbols = buildSymbolTable(IMP_definition)

IMP_symbols['_,_']          = assocWithUnit(' , ', '')
IMP_symbols['.List{"_,_"}'] = constLabel('')

kast_term = readKastTerm(sys.argv[2])

if isKRule(kast_term):
    kast_term = minimizeRule(kast_term)
    defn_name = sys.argv[2][:-5].split('/')[2]
    mod = KFlatModule(defn_name.upper(), [KImport('IMP', True)], [kast_term])
    kast_term = KDefinition(defn_name, [mod], requires = [KRequire('imp.k')])
elif isKClaim(kast_term):
    kast_term = minimizeRule(kast_term)
    defn_name = sys.argv[2][:-5].split('/')[2]
    mod = KFlatModule(defn_name.upper(), [KImport('IMP', True)], [kast_term])
    kast_term = KDefinition(defn_name, [mod], requires = [KRequire('imp.k')])
elif isKApply(kast_term):
    kast_term = simplifyBool(kast_term)

print(prettyPrintKast(kast_term, IMP_symbols, debug = True))
