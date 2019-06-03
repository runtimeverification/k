#!/usr/bin/env python3

import sys
import kast

def writeSpecFile(specName, module, symbolTable, subDir = None):
    specFile = specName + ".k"
    specText = prettyPrintKast(module, symbolTable)
    if subDir is not None:
        specFile = subDir + "/" + specFile
    with open(specFile, "w") as sfile:
        sfile.write(prettyPrintKast(module, symbolTable))
    return (specFile, specText)

def proveRules(specName, kRules, symbolTable, proveArgs, subDir = None):
    writtenRules = [ minimizeRule(kRule) for kRule in kRules ]
    if len(writtenRules) == 0:
        notif("No rules to prove!!")
        return False
    kModule = KModule(specName.upper() + "-SPEC", [KImport("EVM")], writtenRules)
    (specFile, specText) = writeSpecFile(specName + "-spec", kModule, symbolTable, subDir = subDir)
    notif("Attempting to prove rules:")
    print(specText)
    sys.stdout.flush()
    kproveProc = subprocess.run(["./kevm", "prove", "--backend", "java", specFile] + proveArgs)
    print()
    if kproveProc.returncode == 0:
        notif("Proof success!!")
        return True
    else:
        notif("Proof failure!!")
        return False
