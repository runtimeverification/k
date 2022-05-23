import json
import logging
import os
from pathlib import Path
from subprocess import CalledProcessError, CompletedProcess
from typing import Final, Iterable, List, Optional

from ..cli_utils import (
    check_dir_path,
    check_file_path,
    gen_file_timestamp,
    run_process,
)
from ..kast import KAst, KDefinition, KFlatModule, KImport, KRequire
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
    return run_process(run_args, _LOGGER)


class KProve(KPrint):
    """Given a kompiled directory and a main file name, build a prover for it.
    """

    def __init__(self, kompiled_directory, main_file_name, use_directory=None):
        super(KProve, self).__init__(kompiled_directory)
        self.directory = Path(self.kompiled_directory).parent
        self.use_directory = (self.directory / 'kprove') if use_directory is None else Path(use_directory)
        self.use_directory.mkdir(parents=True, exist_ok=True)
        self.main_file_name = main_file_name
        self.prover = ['kprovex']
        self.prover_args = []
        with open(self.kompiled_directory / 'backend.txt', 'r') as ba:
            self.backend = ba.read()
        with open(self.kompiled_directory / 'mainModule.txt', 'r') as mm:
            self.main_module = mm.read()

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
        command += ['--definition', str(self.kompiled_directory), '-I', str(self.directory), '--spec-module', spec_module_name, '--output', 'json']
        command += [c for c in self.prover_args]
        command += args

        command_env = os.environ.copy()
        command_env['KORE_EXEC_OPTS'] = ' '.join(haskell_args + haskell_log_args)

        proc_output: str
        try:
            proc_output = run_process(command, _LOGGER, env=command_env).stdout
        except CalledProcessError as err:
            if err.returncode != 1:
                raise RuntimeError(f'Command kprovex exited with code {err.returncode} for: {spec_file}', err.stdout, err.stderr)
            proc_output = err.stdout

        if not dry_run:

            finalState = KAst.from_dict(json.loads(proc_output)['term'])
            if finalState == mlTop() and len(_getAppliedAxiomList(log_file)) == 0 and not allow_zero_step:
                raise ValueError(f'Proof took zero steps, likely the LHS is invalid: {spec_file}')

            return finalState

    def prove_claim(self, claim, claim_id, lemmas=[], args=[], haskell_args=[], log_axioms_file=None, allow_zero_step=False):
        self._write_claim_definition(claim, claim_id, lemmas=lemmas)
        return self.prove(self.use_directory / (claim_id.lower() + '-spec.k'), claim_id.upper() + '-SPEC', args=args, haskell_args=haskell_args, log_axioms_file=log_axioms_file, allow_zero_step=allow_zero_step)

    def _write_claim_definition(self, claim, claim_id, lemmas=[], rule=False):
        """Given a K claim, write the definition file needed for the prover to it.

        -   Input: KAST representation of a claim to prove, and an identifier for said claim.
        -   Output: Write to filesystem the specification with the claim.
        """
        tmpClaim = self.use_directory / (claim_id.lower() if rule else (claim_id.lower() + '-spec'))
        tmpModuleName = claim_id.upper() if rule else (claim_id.upper() + '-SPEC')
        tmpClaim = tmpClaim.with_suffix('.k')
        with open(tmpClaim, 'w') as tc:
            claimModule = KFlatModule(tmpModuleName, lemmas + [claim], imports=[KImport(self.main_module, True)])
            claimDefinition = KDefinition(tmpModuleName, [claimModule], requires=[KRequire(self.main_file_name)])
            tc.write(gen_file_timestamp() + '\n')
            tc.write(self.pretty_print(claimDefinition) + '\n\n')
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
