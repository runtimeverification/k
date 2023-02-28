import json
import logging
import os
from enum import Enum
from itertools import chain
from pathlib import Path
from subprocess import CalledProcessError, CompletedProcess
from tempfile import NamedTemporaryFile
from typing import Final, Iterable, List, Mapping, Optional, Tuple

from ..cli_utils import BugReport, check_dir_path, check_file_path, gen_file_timestamp, run_process
from ..cterm import CTerm, build_claim
from ..kast.inner import KInner
from ..kast.manip import extract_subst, flatten_label, free_vars
from ..kast.outer import KClaim, KDefinition, KFlatModule, KFlatModuleList, KImport, KRequire, KRule, KSentence
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


class KoreExecLogFormat(Enum):
    STANDARD = 'standard'
    ONELINE = 'oneline'


def _kprove(
    spec_file: Path,
    *,
    command: Iterable[str] = ('kprove',),
    kompiled_dir: Optional[Path] = None,
    spec_module_name: Optional[str] = None,
    md_selector: Optional[str] = None,
    include_dirs: Iterable[Path] = (),
    emit_json_spec: Optional[Path] = None,
    output: Optional[KProveOutput] = None,
    dry_run: bool = False,
    args: Iterable[str] = (),
    env: Optional[Mapping[str, str]] = None,
    check: bool = True,
    depth: Optional[int] = None,
) -> CompletedProcess:
    check_file_path(spec_file)

    for include_dir in include_dirs:
        check_dir_path(include_dir)

    if depth is not None and depth < 0:
        raise ValueError(f'Argument "depth" must be non-negative, got: {depth}')

    typed_args = _build_arg_list(
        kompiled_dir=kompiled_dir,
        spec_module_name=spec_module_name,
        md_selector=md_selector,
        include_dirs=include_dirs,
        emit_json_spec=emit_json_spec,
        output=output,
        dry_run=dry_run,
        depth=depth,
    )

    try:
        run_args = tuple(chain(command, [str(spec_file)], typed_args, args))
        return run_process(run_args, logger=_LOGGER, env=env, check=check)
    except CalledProcessError as err:
        raise RuntimeError(
            f'Command kprove exited with code {err.returncode} for: {spec_file}', err.stdout, err.stderr
        ) from err


def _build_arg_list(
    *,
    kompiled_dir: Optional[Path],
    spec_module_name: Optional[str],
    md_selector: Optional[str],
    include_dirs: Iterable[Path],
    emit_json_spec: Optional[Path],
    output: Optional[KProveOutput],
    dry_run: bool,
    depth: Optional[int],
) -> List[str]:
    args = []

    if kompiled_dir:
        args += ['--definition', str(kompiled_dir)]

    if spec_module_name:
        args += ['--spec-module', spec_module_name]

    if md_selector:
        args += ['--md-selector', md_selector]

    for include_dir in include_dirs:
        args += ['-I', str(include_dir)]

    if emit_json_spec:
        args += ['--emit-json-spec', str(emit_json_spec)]

    if output:
        args += ['--output', output.value]

    if dry_run:
        args.append('--dry-run')

    if depth:
        args += ['--depth', str(depth)]

    return args


class KProve(KPrint):
    main_file: Optional[Path]
    prover: List[str]
    prover_args: List[str]

    def __init__(
        self,
        definition_dir: Path,
        main_file: Optional[Path] = None,
        use_directory: Optional[Path] = None,
        command: str = 'kprove',
        bug_report: Optional[BugReport] = None,
        extra_unparsing_modules: Iterable[KFlatModule] = (),
    ):
        super(KProve, self).__init__(
            definition_dir,
            use_directory=use_directory,
            bug_report=bug_report,
            extra_unparsing_modules=extra_unparsing_modules,
        )
        # TODO: we should not have to supply main_file, it should be read
        # TODO: setting use_directory manually should set temp files to not be deleted and a log message
        self.main_file = main_file
        self.prover = [command]
        self.prover_args = []

    def prove(
        self,
        spec_file: Path,
        spec_module_name: Optional[str] = None,
        args: Iterable[str] = (),
        include_dirs: Iterable[Path] = (),
        md_selector: Optional[str] = None,
        haskell_args: Iterable[str] = (),
        haskell_log_entries: Iterable[str] = (),
        log_axioms_file: Optional[Path] = None,
        allow_zero_step: bool = False,
        dry_run: bool = False,
        depth: Optional[int] = None,
        haskell_log_format: KoreExecLogFormat = KoreExecLogFormat.ONELINE,
        haskell_log_debug_transition: bool = True,
    ) -> KInner:
        log_file = spec_file.with_suffix('.debug-log') if log_axioms_file is None else log_axioms_file
        if log_file.exists():
            log_file.unlink()
        haskell_log_entries = unique(
            list(haskell_log_entries) + (['DebugTransition'] if haskell_log_debug_transition else [])
        )
        haskell_log_args = [
            '--log',
            str(log_file),
            '--log-format',
            haskell_log_format.value,
            '--log-entries',
            ','.join(haskell_log_entries),
        ]

        kore_exec_opts = ' '.join(list(haskell_args) + haskell_log_args)
        _LOGGER.debug(f'export KORE_EXEC_OPTS={kore_exec_opts!r}')
        env = os.environ.copy()
        env['KORE_EXEC_OPTS'] = kore_exec_opts

        proc_result = _kprove(
            spec_file=spec_file,
            command=self.prover,
            kompiled_dir=self.definition_dir,
            spec_module_name=spec_module_name,
            include_dirs=include_dirs,
            md_selector=md_selector,
            output=KProveOutput.JSON,
            dry_run=dry_run,
            args=self.prover_args + list(args),
            env=env,
            check=False,
            depth=depth,
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
        depth: Optional[int] = None,
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
            depth=depth,
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
        log_axioms_file: Optional[Path] = None,
        allow_zero_step: bool = False,
        depth: Optional[int] = None,
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
            depth=depth,
        )
        next_states = list(unique(var_map(ns) for ns in flatten_label('#Or', next_state) if not is_top(ns)))
        constraint_subst, _ = extract_subst(init_cterm.kast)
        next_states = [mlAnd([constraint_subst.unapply(ns), constraint_subst.ml_pred]) for ns in next_states]
        return next_states if len(next_states) > 0 else [mlTop()]

    def get_claims(
        self,
        spec_file: Path,
        spec_module_name: Optional[str] = None,
        include_dirs: Iterable[Path] = (),
        md_selector: Optional[str] = None,
        claim_labels: Optional[Iterable[str]] = None,
        exclude_claim_labels: Optional[Iterable[str]] = None,
    ) -> List[KClaim]:
        with NamedTemporaryFile('w', dir=self.use_directory) as ntf:
            self.prove(
                spec_file,
                spec_module_name=spec_module_name,
                include_dirs=include_dirs,
                md_selector=md_selector,
                dry_run=True,
                args=['--emit-json-spec', ntf.name],
            )
            flat_module_list = KFlatModuleList.from_dict(json.loads(Path(ntf.name).read_text())['term'])

        all_claims = {c.label: c for m in flat_module_list.modules for c in m.claims}

        unfound_labels = []
        claim_labels = list(all_claims.keys()) if claim_labels is None else claim_labels
        exclude_claim_labels = [] if exclude_claim_labels is None else exclude_claim_labels
        unfound_labels.extend([cl for cl in claim_labels if cl not in all_claims])
        unfound_labels.extend([cl for cl in exclude_claim_labels if cl not in all_claims])
        if len(unfound_labels) > 0:
            raise ValueError(f'Claim labels not found: {unfound_labels}')

        return [all_claims[cl] for cl in all_claims if cl in claim_labels and cl not in exclude_claim_labels]

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
