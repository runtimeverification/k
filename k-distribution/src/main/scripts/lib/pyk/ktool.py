#!/usr/bin/env python3

import os
import subprocess

from .kastManip import *

class KPrint:
    """Given a kompiled directory, build an unparser for it.
    """

    def __init__(self, kompiledDirectory):
        self.kompiledDirectory = kompiledDirectory
        self.definition        = readKastTerm(self.kompiledDirectory + '/compiled.json')
        self.symbolTable       = buildSymbolTable(self.definition, opinionated = True)

    def prettyPrint(self, kast):
        """Given a KAST term, pretty-print it using the current definition.

        -   Input: KAST term in JSON.
        -   Output: Best-effort pretty-printed representation of the KAST term.
        """
        return prettyPrintKast(kast, self.symbolTable)

class KProve(KPrint):
    """Given a kompiled directory and a main file name, build a prover for it.
    """

    def __init__(self, kompiledDirectory, mainFileName, useDirectory = None):
        super(KProve, self).__init__(kompiledDirectory)
        self.directory      = '/'.join(self.kompiledDirectory.split('/')[0:-1])
        self.useDirectory   = self.directory + '/kprove' if useDirectory is None else useDirectory
        if not os.path.exists(self.useDirectory):
            os.makedirs(self.useDirectory)
        self.mainFileName   = mainFileName
        self.prover         = [ 'kprovex' ]
        self.proverArgs     = [ ]
        with open(self.kompiledDirectory + '/backend.txt', 'r') as ba:
            self.backend    = ba.read()
        with open(self.kompiledDirectory + '/mainModule.txt', 'r') as mm:
            self.mainModule = mm.read()

    def prove(self, specFile, specModuleName, args = [], haskellArgs = [], logAxiomsFile = None):
        """Given the specification to prove and arguments for the prover, attempt to prove it.

        -   Input: Specification file name, specification module name, optionall arguments, haskell backend arguments, and file to log axioms to.
        -   Output: KAST represenation of output of prover, or crashed process.
        """
        logFile = specFile + '.debug-log' if logAxiomsFile is None else logAxiomsFile
        if os.path.exists(logFile):
            os.remove(logFile)
        haskellLogArgs = [ '--log' , logFile , '--log-format'  , 'oneline' , '--log-entries' , 'DebugTransition' ]
        command  = [ c for c in self.prover ]
        command += [ specFile ]
        command += [ '--backend' , self.backend , '--directory' , self.directory , '-I' , self.directory , '--spec-module' , specModuleName , '--output' , 'json' ]
        command += [ c for c in self.proverArgs ]
        command += args
        commandEnv                   = os.environ.copy()
        commandEnv['KORE_EXEC_OPTS'] = ' '.join(haskellArgs + haskellLogArgs)
        notif(' '.join(command))
        process          = subprocess.Popen(command, stdout = subprocess.PIPE, stderr = subprocess.PIPE, universal_newlines = True, env = commandEnv)
        (stdout, stderr) = process.communicate(input = None)
        try:
            finalState = json.loads(stdout)['term']
        except:
            sys.stderr.write(stdout + '\n')
            sys.stderr.write(stderr + '\n')
            fatal('Exiting...', exitCode = process.returncode)
        if finalState == KConstant('#Top') and len(getAppliedAxiomList(logFile)) == 0:
            fatal('Proof took zero steps, likely the LHS is invalid: ' + specFile)
        return finalState

    def writeClaimDefinition(self, claim, claimId, rule = False):
        """Given a K claim, write the definition file needed for the prover to it.

        -   Input: KAST representation of a claim to prove, and an identifier for said claim.
        -   Output: Write to filesystem the specification with the claim.
        """
        tmpClaim      = self.useDirectory + '/' + claimId.lower()
        tmpModuleName = claimId.upper()
        if not rule:
            tmpClaim      += '-spec'
            tmpModuleName += '-SPEC'
        tmpClaim += '.k'
        with open(tmpClaim, 'w') as tc:
            claimModule     = KFlatModule(tmpModuleName, [self.mainModule], [claim])
            claimDefinition = KDefinition(tmpModuleName, [claimModule], requires = [KRequire(self.mainFileName)])
            tc.write(genFileTimestamp() + '\n')
            tc.write(self.prettyPrint(claimDefinition) + '\n\n')
            tc.flush()
        notif('Wrote claim file: ' + tmpClaim)

    def proveClaim(self, claim, claimId, args = [], haskellArgs = [], logAxiomsFile = None, dryRun = False):
        """Given a K claim, write the definition needed for the prover, and attempt to prove it.

        -   Input: KAST representation of a claim to prove, and an identifer for said claim.
        -   Output: KAST representation of final state the prover supplies for it.
        """
        self.writeClaimDefinition(claim, claimId)
        if not dryRun:
            return self.prove(self.useDirectory + '/' + claimId.lower() + '-spec.k', claimId.upper() + '-SPEC', args = args, haskellArgs = haskellArgs, logAxiomsFile = logAxiomsFile)
        return KConstant('#Top')
