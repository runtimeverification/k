import json
import os
import subprocess
import sys
from pathlib import Path
from typing import List

from .cli_utils import fatal, gen_file_timestamp, notif
from .kast import (
    KAst,
    KDefinition,
    KFlatModule,
    KImport,
    KRequire,
    buildSymbolTable,
    flattenLabel,
    prettyPrintKast,
    readKastTerm,
)
from .prelude import mlTop
from .utils import hash_str


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


class KProve(KPrint):
    """Given a kompiled directory and a main file name, build a prover for it.
    """

    def __init__(self, kompiledDirectory, mainFileName, useDirectory=None):
        super(KProve, self).__init__(kompiledDirectory)
        self.directory = Path(self.kompiledDirectory).parent
        self.useDirectory = (self.directory / 'kprove') if useDirectory is None else Path(useDirectory)
        self.useDirectory.mkdir(parents=True, exist_ok=True)
        self.mainFileName = mainFileName
        self.prover = ['kprovex']
        self.proverArgs = []
        with open(self.kompiledDirectory / 'backend.txt', 'r') as ba:
            self.backend = ba.read()
        with open(self.kompiledDirectory / 'mainModule.txt', 'r') as mm:
            self.mainModule = mm.read()

    def prove(self, specFile, specModuleName, args=[], haskellArgs=[], logAxiomsFile=None, allowZeroStep=False):
        """Given the specification to prove and arguments for the prover, attempt to prove it.

        -   Input: Specification file name, specification module name, optionall arguments, haskell backend arguments, and file to log axioms to.
        -   Output: KAST represenation of output of prover, or crashed process.
        """
        logFile = specFile.with_suffix('.debug-log') if logAxiomsFile is None else logAxiomsFile
        if logFile.exists():
            logFile.unlink()
        haskellLogArgs = ['--log', str(logFile), '--log-format', 'oneline', '--log-entries', 'DebugTransition']
        command = [c for c in self.prover]
        command += [str(specFile)]
        command += ['--backend', self.backend, '--directory', str(self.directory), '-I', str(self.directory), '--spec-module', specModuleName, '--output', 'json']
        command += [c for c in self.proverArgs]
        command += args
        commandEnv = os.environ.copy()
        commandEnv['KORE_EXEC_OPTS'] = ' '.join(haskellArgs + haskellLogArgs)
        notif(' '.join(command))
        process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True, env=commandEnv)
        stdout, stderr = process.communicate(input=None)
        try:
            finalState = KAst.from_dict(json.loads(stdout)['term'])
        except Exception:
            sys.stderr.write(stdout + '\n')
            sys.stderr.write(stderr + '\n')
            fatal(f'Exiting: process returned {process.returncode}')
        if finalState == mlTop() and len(_getAppliedAxiomList(logFile)) == 0 and not allowZeroStep:
            fatal('Proof took zero steps, likely the LHS is invalid: ' + str(specFile))
        return finalState

    def proveClaim(self, claim, claimId, lemmas=[], args=[], haskellArgs=[], logAxiomsFile=None, allowZeroStep=False):
        """Given a K claim, write the definition needed for the prover, and attempt to prove it.

        -   Input: KAST representation of a claim to prove, and an identifer for said claim.
        -   Output: KAST representation of final state the prover supplies for it.
        """
        self._writeClaimDefinition(claim, claimId, lemmas=lemmas)
        return self.prove(self.useDirectory / (claimId.lower() + '-spec.k'), claimId.upper() + '-SPEC', args=args, haskellArgs=haskellArgs, logAxiomsFile=logAxiomsFile, allowZeroStep=allowZeroStep)

    def proveClaimNoBranching(self, claim, claimId, args=[], haskellArgs=[], logAxiomsFile=None, maxDepth=1000, allowZeroStep=False):
        """Given a K claim, attempt to prove it, but do not allow the prover to branch.

        -   Input: KAST representation of a claim to prove, and identifier for said claim.
        -   Output: KAST representation of final state of prover.
        """
        logFileName = logAxiomsFile if logAxiomsFile is not None else (self.useDirectory / claimId.lower()).with_suffix('.debug.log')
        nextState = self.proveClaim(claim, claimId, args=(args + ['--branching-allowed', '1', '--depth', str(maxDepth)]), haskellArgs=haskellArgs, logAxiomsFile=logFileName, allowZeroStep=allowZeroStep)
        depth = 0
        for axioms in _getAppliedAxiomList(str(logFileName)):
            depth += 1
            if len(axioms) > 1:
                break
        nextStates = flattenLabel('#Or', nextState)
        return (depth, nextStates)

    def _writeClaimDefinition(self, claim, claimId, lemmas=[], rule=False):
        """Given a K claim, write the definition file needed for the prover to it.

        -   Input: KAST representation of a claim to prove, and an identifier for said claim.
        -   Output: Write to filesystem the specification with the claim.
        """
        tmpClaim = self.useDirectory / (claimId.lower() if rule else (claimId.lower() + '-spec'))
        tmpModuleName = claimId.upper() if rule else (claimId.upper() + '-SPEC')
        tmpClaim = tmpClaim.with_suffix('.k')
        with open(tmpClaim, 'w') as tc:
            claimModule = KFlatModule(tmpModuleName, lemmas + [claim], imports=[KImport(self.mainModule, True)])
            claimDefinition = KDefinition(tmpModuleName, [claimModule], requires=[KRequire(self.mainFileName)])
            tc.write(gen_file_timestamp() + '\n')
            tc.write(self.prettyPrint(claimDefinition) + '\n\n')
            tc.flush()
        notif('Wrote claim file: ' + str(tmpClaim) + '.')


def _getAppliedAxiomList(debugLogFile: Path) -> List[List[str]]:
    axioms = []
    next_axioms = []
    with open(debugLogFile, 'r') as logFile:
        for line in logFile:
            if line.find('DebugTransition') > 0:
                if line.find('after  apply axioms:') > 0:
                    next_axioms.append(line[line.find('after  apply axioms:') + len('after  apply axioms:'):])
                elif len(next_axioms) > 0:
                    axioms.append(next_axioms)
                    next_axioms = []
    return axioms
