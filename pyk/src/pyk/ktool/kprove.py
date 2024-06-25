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
from ..cterm import CTerm
from ..kast import kast_term
from ..kast.inner import KInner
from ..kast.manip import flatten_label
from ..kast.outer import KDefinition, KFlatModule, KFlatModuleList, KImport, KRequire
from ..kore.rpc import KoreExecLogFormat
from ..prelude.ml import is_top
from ..utils import gen_file_timestamp, run_process
from . import TypeInferenceMode
from .claim_index import ClaimIndex
from .kprint import KPrint

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable, Iterator, Mapping
    from subprocess import CompletedProcess
    from typing import Final

    from ..kast.outer import KClaim, KRule, KRuleLike
    from ..kast.pretty import SymbolTable
    from ..kcfg import KCFGExplore
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
            f'Command kprove exited with code {err.returncode} for: {spec_file}', err.stdout, err.stderr, err
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

    def get_claim_modules(
        self,
        spec_file: Path,
        spec_module_name: str | None = None,
        include_dirs: Iterable[Path] = (),
        md_selector: str | None = None,
        type_inference_mode: TypeInferenceMode | None = None,
    ) -> KFlatModuleList:
        with self._temp_file(prefix=f'{spec_file.name}.parsed.json.') as ntf:
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
            json_data = json.loads(Path(ntf.name).read_text())

        return KFlatModuleList.from_dict(kast_term(json_data))

    def get_claim_index(
        self,
        spec_file: Path,
        spec_module_name: str | None = None,
        include_dirs: Iterable[Path] = (),
        md_selector: str | None = None,
        type_inference_mode: TypeInferenceMode | None = None,
    ) -> ClaimIndex:
        module_list = self.get_claim_modules(
            spec_file=spec_file,
            spec_module_name=spec_module_name,
            include_dirs=include_dirs,
            md_selector=md_selector,
            type_inference_mode=type_inference_mode,
        )
        return ClaimIndex.from_module_list(module_list)

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
        claim_index = self.get_claim_index(
            spec_file=spec_file,
            spec_module_name=spec_module_name,
            include_dirs=include_dirs,
            md_selector=md_selector,
            type_inference_mode=type_inference_mode,
        )

        labels = claim_index.labels(
            include=claim_labels,
            exclude=exclude_claim_labels,
            with_depends=include_dependencies,
        )

        return [claim_index[label] for label in labels]

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
