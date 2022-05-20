import json
import logging
import os
import subprocess
from pathlib import Path
from subprocess import CalledProcessError, CompletedProcess
from typing import Final, Iterable, List, Optional

from ..cli_utils import check_dir_path, check_file_path, gen_file_timestamp
from ..kast import (
    KAst,
    KDefinition,
    KFlatModule,
    KImport,
    KRequire,
    flattenLabel,
)
from ..prelude import mlTop
from .kprint import KPrint

_LOGGER: Final = logging.getLogger(__name__)


def kprovex(
    spec_file: Path,
    *,
    kompiled_dir: Optional[Path] = None,
    include_dirs: Iterable[Path] = (),
    emit_json_spec: Optional[Path] = None,
    dry_run=False,
) -> None:
    check_file_path(spec_file)

    for include_dir in include_dirs:
        check_dir_path(include_dir)

    args = _build_arg_list(
        kompiled_dir=kompiled_dir,
        include_dirs=include_dirs,
        dry_run=dry_run,
        emit_json_spec=emit_json_spec,
    )

    try:
        _kprovex(str(spec_file), *args)
    except CalledProcessError as err:
        raise RuntimeError(f'Command kprovex exited with code {err.returncode} for: {spec_file}', err.stdout, err.stderr)


def _build_arg_list(
    *,
    kompiled_dir: Optional[Path],
    include_dirs: Iterable[Path],
    emit_json_spec: Optional[Path],
    dry_run: bool,
) -> List[str]:
    args = []

    if kompiled_dir:
        args += ['--definition', str(kompiled_dir)]

    for include_dir in include_dirs:
        args += ['-I', str(include_dir)]

    if emit_json_spec:
        args += ['--emit-json-spec', str(emit_json_spec)]

    if dry_run:
        args.append('--dry-run')

    return args


def _kprovex(spec_file: str, *args: str) -> CompletedProcess:
    run_args = ['kprovex', spec_file] + list(args)
    _LOGGER.info(' '.join(run_args))
    return subprocess.run(run_args, capture_output=True, check=True, text=True)


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
        command += ['--definition', str(self.kompiledDirectory), '-I', str(self.directory), '--spec-module', specModuleName, '--output', 'json']
        command += [c for c in self.proverArgs]
        command += args
        commandEnv = os.environ.copy()
        commandEnv['KORE_EXEC_OPTS'] = ' '.join(haskellArgs + haskellLogArgs)

        _LOGGER.info(' '.join(command))
        proc_output: str
        try:
            proc_output = subprocess.run(command, env=commandEnv, capture_output=True, check=True, text=True).stdout
        except CalledProcessError as err:
            if err.returncode != 1:
                raise RuntimeError(f'Command kprovex exited with code {err.returncode} for: {specFile}', err.stdout, err.stderr)
            proc_output = err.stdout

        finalState = KAst.from_dict(json.loads(proc_output)['term'])
        if finalState == mlTop() and len(_getAppliedAxiomList(logFile)) == 0 and not allowZeroStep:
            raise ValueError(f'Proof took zero steps, likely the LHS is invalid: {specFile}')

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
        _LOGGER.info('Wrote claim file: ' + str(tmpClaim) + '.')


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
