import json
import os
import subprocess
import sys
from pathlib import Path
from subprocess import CompletedProcess, run
from typing import Iterable, List, Optional

from ..cli_utils import (
    check_dir_path,
    check_file_path,
    fatal,
    gen_file_timestamp,
    notif,
)
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

    proc_res = _kprovex(str(spec_file), *args)

    if proc_res.returncode:
        raise RuntimeError(f'Command kprovex failed for: {spec_file}')


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
    notif(' '.join(run_args))
    return run(run_args, capture_output=True, text=True)


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

    def prove(self, spec_file, spec_module_name, args=[], haskell_args=[], log_axioms_file=None, allow_zero_step=False, dry_run=False):
        """Given the specification to prove and arguments for the prover, attempt to prove it.

        -   Input: Specification file name, specification module name, optionall arguments, haskell backend arguments, and file to log axioms to.
        -   Output: KAST represenation of output of prover, or crashed process.
        """
        log_file = spec_file.with_suffix('.debug-log') if log_axioms_file is None else log_axioms_file
        if log_file.exists():
            log_file.unlink()
        haskell_log_args = ['--log', str(log_file), '--log-format', 'oneline', '--log-entries', 'DebugTransition']
        command = [c for c in self.prover]
        command += [str(spec_file)]
        command += ['--definition', str(self.kompiledDirectory), '-I', str(self.directory), '--spec-module', spec_module_name, '--output', 'json']
        command += [c for c in self.proverArgs]
        command += args
        command_env = os.environ.copy()
        command_env['KORE_EXEC_OPTS'] = ' '.join(haskell_args + haskell_log_args)
        notif(' '.join(command))
        process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True, env=command_env)
        stdout, stderr = process.communicate(input=None)
        if not dry_run:
            try:
                final_state = KAst.from_dict(json.loads(stdout)['term'])
            except Exception:
                sys.stderr.write(stdout + '\n')
                sys.stderr.write(stderr + '\n')
                fatal(f'Exiting: process returned {process.returncode}')
            if final_state == mlTop() and len(_getAppliedAxiomList(log_file)) == 0 and not allow_zero_step:
                fatal('Proof took zero steps, likely the LHS is invalid: ' + str(spec_file))
            return final_state

    def proveClaim(self, claim, claimId, lemmas=[], args=[], haskell_args=[], log_axioms_file=None, allow_zero_step=False):
        """Given a K claim, write the definition needed for the prover, and attempt to prove it.

        -   Input: KAST representation of a claim to prove, and an identifer for said claim.
        -   Output: KAST representation of final state the prover supplies for it.
        """
        self._writeClaimDefinition(claim, claimId, lemmas=lemmas)
        return self.prove(self.useDirectory / (claimId.lower() + '-spec.k'), claimId.upper() + '-SPEC', args=args, haskell_args=haskell_args, log_axioms_file=log_axioms_file, allow_zero_step=allow_zero_step)

    def proveClaimNoBranching(self, claim, claimId, args=[], haskell_args=[], log_axioms_file=None, maxDepth=1000, allow_zero_step=False):
        """Given a K claim, attempt to prove it, but do not allow the prover to branch.

        -   Input: KAST representation of a claim to prove, and identifier for said claim.
        -   Output: KAST representation of final state of prover.
        """
        logFileName = log_axioms_file if log_axioms_file is not None else (self.useDirectory / claimId.lower()).with_suffix('.debug.log')
        nextState = self.proveClaim(claim, claimId, args=(args + ['--branching-allowed', '1', '--depth', str(maxDepth)]), haskell_args=haskell_args, log_axioms_file=logFileName, allow_zero_step=allow_zero_step)
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
