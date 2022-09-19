import json
import logging
import os
from enum import Enum
from itertools import chain
from pathlib import Path
from subprocess import CalledProcessError, CompletedProcess
from typing import Final, Iterable, List, Mapping, Optional, Tuple

from ..cli_utils import check_dir_path, check_file_path, gen_file_timestamp, run_process
from ..cterm import CTerm, build_claim
from ..kast import KClaim, KDefinition, KFlatModule, KImport, KInner, KRequire, KRule, KSentence
from ..kastManip import extract_subst, flatten_label, free_vars
from ..prelude.ml import is_top, mlAnd, mlBottom, mlTop
from ..utils import unique
from .kprint import KPrint

_LOGGER: Final = logging.getLogger(__name__)


class KProveOutput(Enum):
    PRETTY = 'pretty'
    PROGAM = 'program'
    KAST = 'KAST'
    BINARY = 'binary'
    JSON = 'json'
    LATEX = 'latex'
    KORE = 'kore'
    NONE = 'none'


def _kprove(
    spec_file: Path,
    *,
    command: Iterable[str] = ('kprove',),
    kompiled_dir: Optional[Path] = None,
    spec_module_name: Optional[str] = None,
    include_dirs: Iterable[Path] = (),
    emit_json_spec: Optional[Path] = None,
    output: Optional[KProveOutput] = None,
    dry_run: bool = False,
    args: Iterable[str] = (),
    env: Optional[Mapping[str, str]] = None,
    check: bool = True,
    profile: bool = False,
) -> CompletedProcess:
    check_file_path(spec_file)

    for include_dir in include_dirs:
        check_dir_path(include_dir)

    typed_args = _build_arg_list(
        kompiled_dir=kompiled_dir,
        spec_module_name=spec_module_name,
        include_dirs=include_dirs,
        emit_json_spec=emit_json_spec,
        output=output,
        dry_run=dry_run,
    )

    try:
        run_args = tuple(chain(command, [str(spec_file)], typed_args, args))
        return run_process(run_args, logger=_LOGGER, env=env, check=check, profile=profile)
    except CalledProcessError as err:
        raise RuntimeError(
            f'Command kprove exited with code {err.returncode} for: {spec_file}', err.stdout, err.stderr
        ) from err


def _build_arg_list(
    *,
    kompiled_dir: Optional[Path],
    spec_module_name: Optional[str],
    include_dirs: Iterable[Path],
    emit_json_spec: Optional[Path],
    output: Optional[KProveOutput],
    dry_run: bool,
) -> List[str]:
    args = []

    if kompiled_dir:
        args += ['--definition', str(kompiled_dir)]

    if spec_module_name:
        args += ['--spec-module', spec_module_name]

    for include_dir in include_dirs:
        args += ['-I', str(include_dir)]

    if emit_json_spec:
        args += ['--emit-json-spec', str(emit_json_spec)]

    if output:
        args += ['--output', output.value]

    if dry_run:
        args.append('--dry-run')

    return args


class KProve(KPrint):
    main_file: Optional[Path]
    prover: List[str]
    prover_args: List[str]
    backend: str
    main_module: str

    def __init__(
        self,
        definition_dir: Path,
        main_file: Optional[Path] = None,
        use_directory: Optional[Path] = None,
        profile: bool = False,
    ):
        super(KProve, self).__init__(definition_dir, use_directory=use_directory, profile=profile)
        # TODO: we should not have to supply main_file, it should be read
        # TODO: setting use_directory manually should set temp files to not be deleted and a log message
        self.main_file = main_file
        self.prover = ['kprove']
        self.prover_args = []
        with open(self.definition_dir / 'backend.txt', 'r') as ba:
            self.backend = ba.read()
        with open(self.definition_dir / 'mainModule.txt', 'r') as mm:
            self.main_module = mm.read()

    def prove(
        self,
        spec_file: Path,
        spec_module_name: Optional[str] = None,
        args: Iterable[str] = (),
        haskell_args: Iterable[str] = (),
        haskell_log_entries: Iterable[str] = (),
        log_axioms_file: Optional[Path] = None,
        allow_zero_step: bool = False,
        dry_run: bool = False,
    ) -> KInner:
        log_file = spec_file.with_suffix('.debug-log') if log_axioms_file is None else log_axioms_file
        if log_file.exists():
            log_file.unlink()
        haskell_log_entries = unique(list(haskell_log_entries) + ['DebugTransition'])
        haskell_log_args = [
            '--log',
            str(log_file),
            '--log-format',
            'oneline',
            '--log-entries',
            ','.join(haskell_log_entries),
        ]

        kore_exec_opts = ' '.join(list(haskell_args) + haskell_log_args)
        _LOGGER.debug(f'export KORE_EXEC_OPTS="{kore_exec_opts}"')
        env = os.environ.copy()
        env['KORE_EXEC_OPTS'] = kore_exec_opts

        proc_result = _kprove(
            spec_file=spec_file,
            command=self.prover,
            kompiled_dir=self.definition_dir,
            spec_module_name=spec_module_name,
            output=KProveOutput.JSON,
            dry_run=dry_run,
            args=self.prover_args + list(args),
            env=env,
            check=False,
            profile=self._profile,
        )

        if proc_result.returncode not in (0, 1):
            raise RuntimeError('kprove failed!')

        if dry_run:
            return mlBottom()

        debug_log = _get_rule_log(log_file)
        final_state = KInner.from_dict(json.loads(proc_result.stdout)['term'])
        if is_top(final_state) and len(debug_log) == 0 and not allow_zero_step:
            raise ValueError(f'Proof took zero steps, likely the LHS is invalid: {spec_file}')
        return final_state

    def prove_claim(
        self,
        claim: KClaim,
        claim_id: str,
        lemmas: Iterable[KRule] = (),
        args: Iterable[str] = (),
        haskell_args: Iterable[str] = (),
        haskell_log_entries: Iterable[str] = (),
        log_axioms_file: Optional[Path] = None,
        allow_zero_step: bool = False,
        dry_run: bool = False,
    ) -> KInner:
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
        )

    # TODO: This should return the empty disjunction `[]` instead of `#Top`.
    # The prover should never return #Bottom, so we can ignore that case.
    # Once those are taken care of, we can change the return type to a CTerm
    def prove_cterm(
        self,
        claim_id: str,
        init_cterm: CTerm,
        target_cterm: CTerm,
        lemmas: Iterable[KRule] = (),
        args: Iterable[str] = (),
        haskell_args: Iterable[str] = (),
        log_axioms_file: Path = None,
        allow_zero_step: bool = False,
    ) -> List[KInner]:
        claim, var_map = build_claim(claim_id, init_cterm, target_cterm, keep_vars=free_vars(init_cterm.kast))
        next_state = self.prove_claim(
            claim,
            claim_id,
            lemmas=lemmas,
            args=args,
            haskell_args=haskell_args,
            log_axioms_file=log_axioms_file,
            allow_zero_step=allow_zero_step,
        )
        next_states = [var_map(ns) for ns in flatten_label('#Or', next_state)]
        constraint_subst, _ = extract_subst(init_cterm.kast)
        next_states = [
            mlAnd([constraint_subst.unapply(ns), constraint_subst.ml_pred]) if ns not in [mlTop(), mlBottom()] else ns
            for ns in next_states
        ]
        return next_states

    def get_claim_basic_block(
        self,
        claim_id: str,
        claim: KClaim,
        lemmas: Iterable[KRule] = (),
        args: Iterable[str] = (),
        haskell_args: Iterable[str] = (),
        max_depth: int = 1000,
    ) -> Tuple[int, bool, KInner]:
        def _is_fatal_error_log_entry(line: str) -> bool:
            decide_predicate_unknown = line.find('(ErrorDecidePredicateUnknown): ErrorDecidePredicateUnknown') >= 0
            return decide_predicate_unknown

        claim_path, claim_module = self._write_claim_definition(claim, claim_id, lemmas=lemmas)
        log_axioms_file = claim_path.with_suffix('.debug.log')
        next_state = self.prove(
            claim_path,
            spec_module_name=claim_module,
            args=list(args) + ['--depth', str(max_depth)],
            haskell_args=(['--execute-to-branch'] + list(haskell_args)),
            log_axioms_file=log_axioms_file,
        )
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

    def _write_claim_definition(self, claim: KClaim, claim_id: str, lemmas: Iterable[KRule] = ()) -> Tuple[Path, str]:
        tmp_claim = self.use_directory / (claim_id.lower() + '-spec')
        tmp_module_name = claim_id.upper() + '-SPEC'
        tmp_claim = tmp_claim.with_suffix('.k')
        sentences: List[KSentence] = []
        sentences.extend(lemmas)
        sentences.append(claim)
        with open(tmp_claim, 'w') as tc:
            claim_module = KFlatModule(tmp_module_name, sentences, imports=[KImport(self.main_module, True)])
            requires = []
            if self.main_file is not None:
                requires += [KRequire(str(self.main_file))]
            claim_definition = KDefinition(tmp_module_name, [claim_module], requires=requires)
            tc.write(gen_file_timestamp() + '\n')
            tc.write(self.pretty_print(claim_definition) + '\n\n')
            tc.flush()
        _LOGGER.info(f'Wrote claim file: {tmp_claim}.')
        return tmp_claim, tmp_module_name


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
