from pathlib import Path

from ..kast import buildSymbolTable, prettyPrintKast, readKastTerm
from ..utils import hash_str


class KPrint:
    """Given a kompiled directory, build an unparser for it.
    """

    def __init__(self, kompiledDirectory):
        self.kompiledDirectory = Path(kompiledDirectory)
        self.definition = readKastTerm(self.kompiledDirectory / 'compiled.json')
        self.symbolTable = buildSymbolTable(self.definition, opinionated=True)
        self.definitionHash = hash_str(self.definition)

    def prettyPrint(self, kast, debug=False):
        """Given a KAST term, pretty-print it using the current definition.

        -   Input: KAST term in JSON.
        -   Output: Best-effort pretty-printed representation of the KAST term.
        """
        return prettyPrintKast(kast, self.symbolTable, debug=debug)
