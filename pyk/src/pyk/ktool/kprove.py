from __future__ import annotations

import json
import logging
import os
import re
from contextlib import contextmanager
from enum import Enum
from itertools import chain
from pathlib import Path
from subprocess import CalledProcessError
from typing import TYPE_CHECKING

from ..cli.utils import check_dir_path, check_file_path
from ..cterm import CTerm, cterm_symbolic
from ..kast import Atts, kast_term
from ..kast.inner import KInner
from ..kast.manip import extract_lhs, flatten_label
from ..kast.outer import KApply, KDefinition, KFlatModule, KFlatModuleList, KImport, KRequire
from ..kcfg.explore import KCFGExplore
from ..kore.rpc import KoreExecLogFormat
from ..prelude.ml import is_top
from ..proof import APRProof, APRProver, EqualityProof, ImpliesProver
from ..utils import gen_file_timestamp, run_process
from . import TypeInferenceMode
from .kprint import KPrint

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable, Iterator, Mapping
    from subprocess import CompletedProcess
    from typing import Final

    from ..cli.pyk import ProveOptions
    from ..kast.outer import KClaim, KRule, KRuleLike
    from ..kast.pretty import SymbolTable
    from ..kcfg.semantics import KCFGSemantics
    from ..kore.rpc import FallbackReason
    from ..proof import Proof, Prover
    from ..utils import BugReport

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
    kompiled_dir: Path | None = None,
    spec_module_name: str | None = None,
    md_selector: str | None = None,
    include_dirs: Iterable[Path] = (),
    emit_json_spec: Path | None = None,
    output: KProveOutput | None = None,
    depth: int | None = None,
    claims: Iterable[str] = (),
    type_inference_mode: str | TypeInferenceMode | None = None,
    temp_dir: Path | None = None,
    haskell_backend_command: str | None = None,
    dry_run: bool = False,
    # --
    args: Iterable[str] = (),
    # --
    env: Mapping[str, str] | None = None,
    check: bool = True,
) -> CompletedProcess:
    check_file_path(spec_file)

    for include_dir in include_dirs:
        check_dir_path(include_dir)

    if depth is not None and depth < 0:
        raise ValueError(f'Argument "depth" must be non-negative, got: {depth}')

    if type_inference_mode is not None:
        type_inference_mode = TypeInferenceMode(type_inference_mode)

    typed_args = _build_arg_list(
        kompiled_dir=kompiled_dir,
        spec_module_name=spec_module_name,
        md_selector=md_selector,
        include_dirs=include_dirs,
        emit_json_spec=emit_json_spec,
        output=output,
        depth=depth,
        claims=claims,
        type_inference_mode=type_inference_mode,
        temp_dir=temp_dir,
        haskell_backend_command=haskell_backend_command,
        dry_run=dry_run,
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
    kompiled_dir: Path | None,
    spec_module_name: str | None,
    md_selector: str | None,
    include_dirs: Iterable[Path],
    emit_json_spec: Path | None,
    output: KProveOutput | None,
    depth: int | None,
    claims: Iterable[str],
    type_inference_mode: TypeInferenceMode | None,
    temp_dir: Path | None,
    haskell_backend_command: str | None,
    dry_run: bool,
) -> list[str]:
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

    if claims:
        args += ['--claims', ','.join(claims)]

    if type_inference_mode:
        args += ['--type-inference-mode', type_inference_mode.value]

    if temp_dir:
        args += ['--temp-dir', str(temp_dir)]

    if haskell_backend_command:
        args += ['--haskell-backend-command', haskell_backend_command]

    if depth:
        args += ['--depth', str(depth)]

    if dry_run:
        args.append('--dry-run')

    return args


class KProve(KPrint):
    main_file: Path | None
    prover: list[str]
    prover_args: list[str]
    _kcfg_explore: KCFGExplore | None

    def __init__(
        self,
        definition_dir: Path,
        main_file: Path | None = None,
        use_directory: Path | None = None,
        command: str = 'kprove',
        bug_report: BugReport | None = None,
        extra_unparsing_modules: Iterable[KFlatModule] = (),
        patch_symbol_table: Callable[[SymbolTable], None] | None = None,
    ):
        super().__init__(
            definition_dir,
            use_directory=use_directory,
            bug_report=bug_report,
            extra_unparsing_modules=extra_unparsing_modules,
            patch_symbol_table=patch_symbol_table,
        )
        # TODO: we should not have to supply main_file, it should be read
        self.main_file = main_file
        self.prover = [command]
        self.prover_args = []
        self._kcfg_explore = None

    def prove(
        self,
        spec_file: Path,
        spec_module_name: str | None = None,
        args: Iterable[str] = (),
        include_dirs: Iterable[Path] = (),
        md_selector: str | None = None,
        haskell_args: Iterable[str] = (),
        depth: int | None = None,
    ) -> list[CTerm]:
        log_file = spec_file.with_suffix('.debug-log')
        if log_file.exists():
            log_file.unlink()
        haskell_log_args = [
            '--log',
            str(log_file),
            '--log-format',
            KoreExecLogFormat.ONELINE.value,
            '--log-entries',
            'DebugTransition',
        ]

        env = os.environ.copy()
        existing_opts = os.getenv('KORE_EXEC_OPTS')
        kore_exec_opts = ' '.join(list(haskell_args) + haskell_log_args + ([existing_opts] if existing_opts else []))
        _LOGGER.debug(f'export KORE_EXEC_OPTS={kore_exec_opts!r}')
        env['KORE_EXEC_OPTS'] = kore_exec_opts

        proc_result = _kprove(
            spec_file=spec_file,
            command=self.prover,
            kompiled_dir=self.definition_dir,
            spec_module_name=spec_module_name,
            include_dirs=include_dirs,
            md_selector=md_selector,
            output=KProveOutput.JSON,
            temp_dir=self.use_directory,
            args=self.prover_args + list(args),
            env=env,
            check=False,
            depth=depth,
        )

        if proc_result.returncode not in (0, 1):
            raise RuntimeError('kprove failed!')

        debug_log = _get_rule_log(log_file)
        final_state = KInner.from_dict(kast_term(json.loads(proc_result.stdout)))
        if is_top(final_state) and len(debug_log) == 0:
            raise ValueError(f'Proof took zero steps, likely the LHS is invalid: {spec_file}')
        return [CTerm.from_kast(disjunct) for disjunct in flatten_label('#Or', final_state)]

    def prove_claim(
        self,
        claim: KClaim,
        claim_id: str,
        lemmas: Iterable[KRule] = (),
        args: Iterable[str] = (),
        haskell_args: Iterable[str] = (),
        depth: int | None = None,
    ) -> list[CTerm]:
        with self._tmp_claim_definition(claim, claim_id, lemmas=lemmas) as (claim_path, claim_module_name):
            return self.prove(
                claim_path,
                spec_module_name=claim_module_name,
                args=args,
                haskell_args=haskell_args,
                depth=depth,
            )

    def prove_claim_rpc(
        self,
        claim: KClaim,
        kcfg_semantics: KCFGSemantics | None = None,
        id: str | None = None,
        port: int | None = None,
        kore_rpc_command: str | Iterable[str] | None = None,
        llvm_definition_dir: Path | None = None,
        smt_timeout: int | None = None,
        smt_retry_limit: int | None = None,
        smt_tactic: str | None = None,
        bug_report: BugReport | None = None,
        haskell_log_format: KoreExecLogFormat = KoreExecLogFormat.ONELINE,
        haskell_log_entries: Iterable[str] = (),
        log_axioms_file: Path | None = None,
        trace_rewrites: bool = False,
        start_server: bool = True,
        maude_port: int | None = None,
        fallback_on: Iterable[FallbackReason] | None = None,
        interim_simplification: int | None = None,
        no_post_exec_simplify: bool = False,
        max_depth: int | None = None,
    ) -> Proof:
        with cterm_symbolic(
            self.definition,
            self.kompiled_kore,
            self.definition_dir,
            id=id,
            port=port,
            kore_rpc_command=kore_rpc_command,
            llvm_definition_dir=llvm_definition_dir,
            smt_timeout=smt_timeout,
            smt_retry_limit=smt_retry_limit,
            smt_tactic=smt_tactic,
            bug_report=bug_report,
            haskell_log_format=haskell_log_format,
            haskell_log_entries=haskell_log_entries,
            log_axioms_file=log_axioms_file,
            trace_rewrites=trace_rewrites,
            start_server=start_server,
            maude_port=maude_port,
            fallback_on=fallback_on,
            interim_simplification=interim_simplification,
            no_post_exec_simplify=no_post_exec_simplify,
        ) as cts:
            kcfg_explore = KCFGExplore(cts, kcfg_semantics=kcfg_semantics)
            proof: Proof
            prover: Prover
            lhs_top = extract_lhs(claim.body)
            if type(lhs_top) is KApply and self.definition.symbols[lhs_top.label.name] in self.definition.functions:
                proof = EqualityProof.from_claim(claim, self.definition)
                prover = ImpliesProver(proof, kcfg_explore)
            else:
                proof = APRProof.from_claim(self.definition, claim, {})
                prover = APRProver(proof, kcfg_explore, execute_depth=max_depth)
            prover.advance_proof()
            if proof.passed:
                _LOGGER.info(f'Proof passed: {proof.id}')
            elif proof.failed:
                _LOGGER.info(f'Proof failed: {proof.id}')
            else:
                _LOGGER.info(f'Proof pending: {proof.id}')
            return proof

    def prove_rpc(
        self,
        options: ProveOptions,
        kcfg_semantics: KCFGSemantics | None = None,
        id: str | None = None,
        port: int | None = None,
        kore_rpc_command: str | Iterable[str] | None = None,
        llvm_definition_dir: Path | None = None,
        smt_timeout: int | None = None,
        smt_retry_limit: int | None = None,
        smt_tactic: str | None = None,
        bug_report: BugReport | None = None,
        haskell_log_format: KoreExecLogFormat = KoreExecLogFormat.ONELINE,
        haskell_log_entries: Iterable[str] = (),
        log_axioms_file: Path | None = None,
        trace_rewrites: bool = False,
        start_server: bool = True,
        maude_port: int | None = None,
        fallback_on: Iterable[FallbackReason] | None = None,
        interim_simplification: int | None = None,
        no_post_exec_simplify: bool = False,
        max_depth: int | None = None,
    ) -> list[Proof]:
        def _prove_claim_rpc(claim: KClaim) -> Proof:
            return self.prove_claim_rpc(
                claim,
                kcfg_semantics=kcfg_semantics,
                id=id,
                port=port,
                kore_rpc_command=kore_rpc_command,
                llvm_definition_dir=llvm_definition_dir,
                smt_timeout=smt_timeout,
                smt_retry_limit=smt_retry_limit,
                smt_tactic=smt_tactic,
                bug_report=bug_report,
                haskell_log_format=haskell_log_format,
                haskell_log_entries=haskell_log_entries,
                log_axioms_file=log_axioms_file,
                trace_rewrites=trace_rewrites,
                start_server=start_server,
                maude_port=maude_port,
                fallback_on=fallback_on,
                interim_simplification=interim_simplification,
                no_post_exec_simplify=no_post_exec_simplify,
                max_depth=max_depth,
            )

        all_claims = self.get_claims(
            options.spec_file,
            spec_module_name=options.spec_module,
            claim_labels=options.claim_labels,
            exclude_claim_labels=options.exclude_claim_labels,
            type_inference_mode=options.type_inference_mode,
        )
        if all_claims is None:
            raise ValueError(f'No claims found in file: {options.spec_file}')
        return [_prove_claim_rpc(claim) for claim in all_claims]

    def get_claim_modules(
        self,
        spec_file: Path,
        spec_module_name: str | None = None,
        include_dirs: Iterable[Path] = (),
        md_selector: str | None = None,
        type_inference_mode: TypeInferenceMode | None = None,
    ) -> KFlatModuleList:
        with self._temp_file() as ntf:
            _kprove(
                spec_file=spec_file,
                kompiled_dir=self.definition_dir,
                spec_module_name=spec_module_name,
                include_dirs=include_dirs,
                md_selector=md_selector,
                output=KProveOutput.JSON,
                temp_dir=self.use_directory,
                dry_run=True,
                type_inference_mode=type_inference_mode,
                args=['--emit-json-spec', ntf.name],
            )
            return KFlatModuleList.from_dict(kast_term(json.loads(Path(ntf.name).read_text())))

    def get_claims(
        self,
        spec_file: Path,
        spec_module_name: str | None = None,
        include_dirs: Iterable[Path] = (),
        md_selector: str | None = None,
        claim_labels: Iterable[str] | None = None,
        exclude_claim_labels: Iterable[str] | None = None,
        include_dependencies: bool = True,
        type_inference_mode: TypeInferenceMode | None = None,
    ) -> list[KClaim]:
        flat_module_list = self.get_claim_modules(
            spec_file=spec_file,
            spec_module_name=spec_module_name,
            include_dirs=include_dirs,
            md_selector=md_selector,
            type_inference_mode=type_inference_mode,
        )

        _module_names = [module.name for module in flat_module_list.modules]

        def _get_claim_module(_label: str) -> str | None:
            if _label.find('.') > 0 and _label.split('.')[0] in _module_names:
                return _label.split('.')[0]
            return None

        all_claims = {
            claim.label: (claim, module.name) for module in flat_module_list.modules for claim in module.claims
        }

        claim_labels = list(all_claims.keys()) if claim_labels is None else list(claim_labels)
        exclude_claim_labels = [] if exclude_claim_labels is None else list(exclude_claim_labels)

        final_claims: dict[str, KClaim] = {}
        unfound_labels: list[str] = []
        while len(claim_labels) > 0:
            claim_label = claim_labels.pop(0)
            if claim_label in final_claims or claim_label in exclude_claim_labels:
                continue
            if claim_label not in all_claims:
                claim_label = f'{flat_module_list.main_module}.{claim_label}'
            if claim_label not in all_claims:
                unfound_labels.append(claim_label)
                continue

            _claim, _module_name = all_claims[claim_label]
            _updated_dependencies: list[str] = []
            for _dependency_label in _claim.dependencies:
                if _get_claim_module(_dependency_label) is None:
                    _dependency_label = f'{_module_name}.{_dependency_label}'
                _updated_dependencies.append(_dependency_label)
            if len(_updated_dependencies) > 0:
                claim_labels.extend(_updated_dependencies)
                _claim = _claim.let(att=_claim.att.update([Atts.DEPENDS(','.join(_updated_dependencies))]))

            final_claims[claim_label] = _claim

        if len(unfound_labels) > 0:
            raise ValueError(f'Claim labels not found: {unfound_labels}')

        return list(final_claims.values())

    @contextmanager
    def _tmp_claim_definition(
        self,
        claim: KClaim,
        claim_id: str,
        lemmas: Iterable[KRule] = (),
    ) -> Iterator[tuple[Path, str]]:
        with self._temp_file(suffix='-spec.k') as ntf:
            tmp_claim_file = Path(ntf.name)
            tmp_module_name = tmp_claim_file.stem.removesuffix('-spec').rstrip('_').replace('_', '-').upper() + '-SPEC'
            tmp_module_name = re.sub(r'-+', '-', tmp_module_name)

            sentences: list[KRuleLike] = []
            sentences += lemmas
            sentences += [claim]

            claim_module = KFlatModule(tmp_module_name, sentences, imports=[KImport(self.main_module, True)])
            requires = [KRequire(str(self.main_file))] if self.main_file is not None else []
            claim_definition = KDefinition(tmp_module_name, [claim_module], requires=requires)

            ntf.write(gen_file_timestamp() + '\n')
            ntf.write(self.pretty_print(claim_definition) + '\n\n')
            ntf.flush()

            _LOGGER.info(f'Wrote claim file: {tmp_claim_file}')
            yield tmp_claim_file, tmp_module_name


def _get_rule_log(debug_log_file: Path) -> list[list[tuple[str, bool, int]]]:
    # rule_loc, is_success, ellapsed_time_since_start
    def _get_rule_line(_line: str) -> tuple[str, bool, int] | None:
        if _line.startswith('kore-exec: ['):
            time = int(_line.split('[')[1].split(']')[0])
            if _line.find('(DebugTransition): after  apply axioms: ') > 0:
                rule_name = ':'.join(_line.split(':')[-4:]).strip()
                return (rule_name, True, time)
            elif _line.find('(DebugAttemptedRewriteRules): ') > 0:
                rule_name = ':'.join(_line.split(':')[-4:]).strip()
                return (rule_name, False, time)
        return None

    log_lines: list[tuple[str, bool, int]] = []
    with open(debug_log_file) as log_file:
        for line in log_file.read().split('\n'):
            if processed_line := _get_rule_line(line):
                log_lines.append(processed_line)

    # rule_loc, is_success, time_delta
    axioms: list[list[tuple[str, bool, int]]] = [[]]
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
