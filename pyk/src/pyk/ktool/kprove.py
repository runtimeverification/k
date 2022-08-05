import csv
import json
import logging
import os
from pathlib import Path
from subprocess import CalledProcessError, CompletedProcess
from tempfile import TemporaryDirectory
from typing import Dict, Final, Iterable, List, Mapping, Optional, Tuple

from ..cli_utils import (
    check_dir_path,
    check_file_path,
    gen_file_timestamp,
    run_process,
)
from ..kast import (
    KAst,
    KClaim,
    KDefinition,
    KFlatModule,
    KImport,
    KInner,
    KRequire,
    KRule,
    KSentence,
    flatten_label,
)
from ..prelude import mlTop
from ..utils import unique
from .kprint import KPrint

_LOGGER: Final = logging.getLogger(__name__)


def kprove(
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
        _kprove(str(spec_file), *args)
    except CalledProcessError as err:
        raise RuntimeError(f'Command kprove exited with code {err.returncode} for: {spec_file}', err.stdout, err.stderr)


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


def _kprove(spec_file: str, *args: str) -> CompletedProcess:
    run_args = ['kprove', spec_file] + list(args)
    return run_process(run_args, _LOGGER)


class KProve(KPrint):

    use_directory: Path
    main_file_name: Optional[str]
    prover: List[str]
    prover_args: List[str]
    backend: str
    main_module: str

    def __init__(self, definition_dir, main_file_name=None, use_directory=None):
        super(KProve, self).__init__(definition_dir)
        if not use_directory:
            _temp_dir = TemporaryDirectory()
            self.use_directory = Path(_temp_dir.name)
        else:
            self.use_directory = Path(use_directory)
            check_dir_path(self.use_directory)
        # TODO: we should not have to supply main_file_name, it should be read
        self.main_file_name = main_file_name
        self.prover = ['kprove']
        self.prover_args = []
        with open(self.definition_dir / 'backend.txt', 'r') as ba:
            self.backend = ba.read()
        with open(self.definition_dir / 'mainModule.txt', 'r') as mm:
            self.main_module = mm.read()

    def prove(
        self,
        spec_file,
        spec_module_name=None,
        args=[],
        haskell_args=[],
        haskell_log_entries=[],
        log_axioms_file=None,
        allow_zero_step=False,
        dry_run=False,
        rule_profile=None,
    ):
        log_file = spec_file.with_suffix('.debug-log') if log_axioms_file is None else log_axioms_file
        if log_file.exists():
            log_file.unlink()
        haskell_log_entries += ['DebugTransition']
        haskell_log_entries += ['DebugAttemptedRewriteRules'] if rule_profile else []
        haskell_log_entries = unique(haskell_log_entries)
        haskell_log_args = ['--log', str(log_file), '--log-format', 'oneline', '--log-entries', ','.join(haskell_log_entries)]
        command = [c for c in self.prover]
        command += [str(spec_file)]
        command += ['--definition', str(self.definition_dir), '--output', 'json']
        command += ['--spec-module', spec_module_name] if spec_module_name is not None else []
        command += ['--dry-run'] if dry_run else []
        command += [c for c in self.prover_args]
        command += args

        kore_exec_opts = ' '.join(haskell_args + haskell_log_args)
        _LOGGER.debug(f'export KORE_EXEC_OPTS="{kore_exec_opts}"')
        command_env = os.environ.copy()
        command_env['KORE_EXEC_OPTS'] = kore_exec_opts

        proc_output: str
        try:
            proc_output = run_process(command, _LOGGER, env=command_env).stdout
        except CalledProcessError as err:
            if err.returncode != 1:
                raise RuntimeError(f'Command kprove exited with code {err.returncode} for: {spec_file}', err.stdout, err.stderr)
            proc_output = err.stdout

        if not dry_run:

            debug_log = _get_rule_log(log_file)

            final_state = KAst.from_dict(json.loads(proc_output)['term'])
            if final_state == mlTop() and len(debug_log) == 0 and not allow_zero_step:
                raise ValueError(f'Proof took zero steps, likely the LHS is invalid: {spec_file}')

            if rule_profile:
                rule_data = _get_rule_profile(debug_log)
                table_lines = []
                total_success_time = 0.0
                total_failure_time = 0.0
                total_success_n = 0.0
                total_failure_n = 0.0
                for rule_name in rule_data:
                    table_line = [rule_name, *rule_data[rule_name]]
                    table_lines.append(table_line)
                    total_success_time += table_line[1]
                    total_failure_time += table_line[4]
                    total_success_n += table_line[2]
                    total_failure_n += table_line[5]
                avg_success_time = total_success_time / total_success_n if total_success_n > 0 else 0.0
                avg_failure_time = total_failure_time / total_failure_n if total_failure_n > 0 else 0.0
                productivity = total_success_time / (total_success_time + total_failure_time)
                table_lines.append(['TOTAL', total_success_time, total_success_n, avg_success_time, total_failure_time, total_failure_n, avg_failure_time, productivity])
                table_lines = sorted(table_lines, key=lambda x: x[1] + x[4])
                with open(rule_profile, 'w') as rp_file:
                    writer = csv.writer(rp_file)
                    writer.writerow(('Rule', 'Total Success Time', '# Successes', 'Avg. Success Time', 'Total Failure Time', '# Failures', 'Avg. Failure Time', 'Productivity'))
                    writer.writerows(table_lines)
                    _LOGGER.info(f'Wrote rule profile: {rule_profile}')

            return final_state

    def prove_claim(
        self,
        claim,
        claim_id,
        lemmas=[],
        args=[],
        haskell_args=[],
        haskell_log_entries=[],
        log_axioms_file=None,
        allow_zero_step=False,
        dry_run=False,
        rule_profile=False,
    ):
        claim_path, claim_module_name = self._write_claim_definition(claim, claim_id, lemmas=lemmas)
        return self.prove(
            claim_path,
            spec_module_name=claim_module_name,
            args=args,
            haskell_args=haskell_args,
            haskell_log_entries=haskell_log_entries,
            log_axioms_file=log_axioms_file,
            allow_zero_step=allow_zero_step,
            dry_run=dry_run,
            rule_profile=rule_profile,
        )

    def get_claim_basic_block(self, claim_id: str, claim: KClaim, lemmas: List[KRule] = [], args: List[str] = [], haskell_args: List[str] = [], max_depth: int = 1000) -> Tuple[int, bool, KInner]:

        def _is_fatal_error_log_entry(line: str) -> bool:
            decide_predicate_unknown = line.find('(ErrorDecidePredicateUnknown): ErrorDecidePredicateUnknown') >= 0
            return decide_predicate_unknown

        claim_path, claim_module = self._write_claim_definition(claim, claim_id, lemmas=lemmas)
        log_axioms_file = claim_path.with_suffix('.debug.log')
        next_state = self.prove(claim_path, spec_module_name=claim_module, args=(args + ['--depth', str(max_depth)]), haskell_args=(['--execute-to-branch'] + haskell_args), log_axioms_file=log_axioms_file)
        if len(flatten_label('#And', next_state)) != 1:
            raise AssertionError(f'get_basic_block execeted 1 state from Haskell backend, got: {next_state}')
        with open(log_axioms_file) as lf:
            log_file = lf.readlines()
        depth = -1
        branching = False
        could_be_branching = False
        rule_count = 0
        _LOGGER.info(f'log_file: {log_axioms_file}')
        for log_line in log_file:
            if _is_fatal_error_log_entry(log_line):
                depth = rule_count
                _LOGGER.warning(f'Fatal backend error: {log_line}')
            elif log_line.find('InfoUnprovenDepth') >= 0 or log_line.find('InfoProvenDepth') >= 0:
                # example:
                # kore-exec: [12718755] Info (InfoProofDepth): InfoUnprovenDepth : 48
                depth = int(log_line.split(':')[-1].strip())
            elif log_line.find('(DebugTransition): after  apply axioms: ') >= 0:
                rule_count += 1
                # example:
                # kore-exec: [24422822] Debug (DebugTransition): after  apply axioms: /home/dev/src/erc20-verification-pr/.build/usr/lib/ktoken/kevm/lib/kevm/include/kframework/evm.md:1858:10-1859:38
                branching = branching or could_be_branching
                could_be_branching = True
            else:
                could_be_branching = False
        return depth, branching, next_state

    def _write_claim_definition(self, claim: KClaim, claim_id: str, lemmas: List[KRule] = []) -> Tuple[Path, str]:
        tmp_claim = self.use_directory / (claim_id.lower() + '-spec')
        tmp_module_name = claim_id.upper() + '-SPEC'
        tmp_claim = tmp_claim.with_suffix('.k')
        sentences: List[KSentence] = []
        sentences.extend(lemmas)
        sentences.append(claim)
        with open(tmp_claim, 'w') as tc:
            claim_module = KFlatModule(tmp_module_name, sentences, imports=[KImport(self.main_module, True)])
            assert self.main_file_name is not None
            claim_definition = KDefinition(tmp_module_name, [claim_module], requires=[KRequire(self.main_file_name)])
            tc.write(gen_file_timestamp() + '\n')
            tc.write(self.pretty_print(claim_definition) + '\n\n')
            tc.flush()
        _LOGGER.debug(f'Wrote claim file: {tmp_claim}.')
        return tmp_claim, tmp_module_name


def _get_rule_profile(debug_log: List[List[Tuple[str, bool, int]]]) -> Mapping[str, Tuple[float, int, float, float, int, float, float]]:

    def _get_single_rule_profile(_rule_log: List[Tuple[float, bool]]) -> Tuple[float, int, float, float, int, float, float]:
        success_time = 0.0
        failure_time = 0.0
        success_n = 0
        failure_n = 0
        for time, success in _rule_log:
            if success:
                success_time += time
                success_n += 1
            else:
                failure_time += time
                failure_n += 1
        success_avg = success_time / success_n if success_n > 0 else 0.0
        failure_avg = failure_time / failure_n if failure_n > 0 else 0.0
        productivity = success_time / (success_time + failure_time)
        return (success_time, success_n, success_avg, failure_time, failure_n, failure_avg, productivity)

    rule_data: Dict[str, List[Tuple[float, bool]]] = {}
    for rule_name, apply_success, apply_time in [rl for rls in debug_log for rl in rls]:
        if rule_name not in rule_data:
            rule_data[rule_name] = []
        rule_data[rule_name].append((apply_time, apply_success))

    return {rule_name: _get_single_rule_profile(rule_data[rule_name]) for rule_name in rule_data}


def _get_rule_log(debug_log_file: Path) -> List[List[Tuple[str, bool, int]]]:

    # rule_loc, is_success, ellapsed_time_since_start
    def _get_rule_line(_line: str) -> Optional[Tuple[str, bool, int]]:
        if _line.startswith('kore-exec: ['):
            time = int(_line.split('[')[1].split(']')[0])
            if _line.find('(DebugTransition): after  apply axioms: ') > 0:
                rule_name = ':'.join(_line.split(':')[-4:]).strip()
                return (rule_name, True, time)
            elif _line.find('(DebugAttemptedRewriteRules): ') > 0:
                rule_name = ':'.join(_line.split(':')[-4:]).strip()
                return (rule_name, False, time)
        return None

    log_lines: List[Tuple[str, bool, int]] = []
    with open(debug_log_file, 'r') as log_file:
        for line in log_file.read().split('\n'):
            if processed_line := _get_rule_line(line):
                log_lines.append(processed_line)

    # rule_loc, is_success, time_delta
    axioms: List[List[Tuple[str, bool, int]]] = [[]]
    just_applied = True
    prev_time = 0
    for rule_name, is_application, rule_time in log_lines:
        rtime = rule_time - prev_time
        prev_time = rule_time
        if not is_application:
            if just_applied:
                axioms.append([])
            just_applied = False
        else:
            just_applied = True
        axioms[-1].append((rule_name, is_application, rtime))

    if len(axioms[-1]) == 0:
        axioms.pop(-1)

    return axioms
