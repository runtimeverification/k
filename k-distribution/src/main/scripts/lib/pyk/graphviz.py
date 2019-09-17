#!/usr/bin/env python3

from .kast      import *
from .kast      import _fatal, _warning, _notif
from .kastManip import readKastTerm

from graphviz import Digraph

def graphvizImports(definitionFile):
    kDefn = readKastTerm(definitionFile + ".json")
    if not isKDefinition(kDefn):
        _fatal("Can only build import graphs for a KDefinition, not a: " + kDefn["node"])
    importGraph = Digraph()
    for module in kDefn["modules"]:
        modName = module["name"]
        importGraph.node(modName)
        for moduleImport in module["imports"]:
            importGraph.edge(modName, moduleImport)
    importGraph.render(definitionFile + "-imports")
    _notif("Wrote graph files: " + definitionFile + "-imports.*")
    return True
