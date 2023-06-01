from __future__ import annotations

import json
import logging
from contextlib import contextmanager
from enum import Enum
from functools import cached_property
from pathlib import Path
from subprocess import CalledProcessError
from tempfile import NamedTemporaryFile
from typing import TYPE_CHECKING

from ..cli_utils import check_dir_path, check_file_path, run_process
from ..kast import kast_term
from ..kast.inner import KInner
from ..kast.outer import read_kast_definition
from ..kast.pretty import PrettyPrinter
from ..konvert import kast_to_kore, kore_to_kast
from ..kore.kompiled import KompiledKore
from ..kore.parser import KoreParser
from ..kore.syntax import App, SortApp

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable, Iterator
    from subprocess import CompletedProcess
    from tempfile import _TemporaryFileWrapper
    from typing import Final

    from ..cli_utils import BugReport
    from ..kast import KAst
    from ..kast.inner import KSort, KToken
    from ..kast.outer import KDefinition, KFlatModule
    from ..kast.pretty import SymbolTable
    from ..kore.syntax import Pattern

_LOGGER: Final = logging.getLogger(__name__)


class KAstInput(Enum):
    PROGRAM = 'program'
    BINARY = 'binary'
    JSON = 'json'
    KAST = 'kast'
    KORE = 'kore'
    RULE = 'rule'


class KAstOutput(Enum):
    PRETTY = 'pretty'
    PROGRAM = 'program'
    KAST = 'kast'
    BINARY = 'binary'
    JSON = 'json'
    LATEX = 'latex'
    KORE = 'kore'
    NONE = 'none'


def _kast(
    file: str | Path | None = None,
    *,
    command: str | None = None,
    definition_dir: str | Path | None = None,
    input: str | KAstInput | None = None,
    output: str | KAstOutput | None = None,
    expression: str | None = None,
    module: str | None = None,
    sort: str | None = None,
    gen_glr_parser: bool = False,
    # ---
    check: bool = True,
) -> CompletedProcess:
    if file is not None:
        file = Path(file)

    if file and not gen_glr_parser:
        check_file_path(file)

    if not file and gen_glr_parser:
        raise ValueError('No output file specified for --gen-glr-parser')

    if definition_dir is not None:
        definition_dir = Path(definition_dir)
        check_dir_path(definition_dir)

    if input is not None:
        input = KAstInput(input)

    if output is not None:
        output = KAstOutput(output)

    args = _build_arg_list(
        file=file,
        command=command,
        definition_dir=definition_dir,
        input=input,
        output=output,
        expression=expression,
        module=module,
        sort=sort,
        gen_glr_parser=gen_glr_parser,
    )

    try:
        return run_process(args, logger=_LOGGER, check=check)
    except CalledProcessError as err:
        raise RuntimeError(
            f'Command kast exited with code {err.returncode} for: {file}', err.stdout, err.stderr
        ) from err


def gen_glr_parser(
    parser_file: str | Path,
    *,
    command: str | None = None,
    definition_dir: str | Path | None = None,
    module: str | None = None,
    sort: str | None = None,
) -> Path:
    parser_file = Path(parser_file)
    _kast(
        file=parser_file,
        command=command,
        definition_dir=definition_dir,
        module=module,
        sort=sort,
        gen_glr_parser=True,
        check=True,
    )
    assert parser_file.is_file()
    return parser_file


def _build_arg_list(
    *,
    file: Path | None,
    command: str | None,
    definition_dir: Path | None,
    input: KAstInput | None,
    output: KAstOutput | None,
    expression: str | None,
    module: str | None,
    sort: str | None,
    gen_glr_parser: bool,
) -> list[str]:
    args = [command if command is not None else 'kast']
    if file:
        args += [str(file)]
    if definition_dir:
        args += ['--definition', str(definition_dir)]
    if input:
        args += ['--input', input.value]
    if output:
        args += ['--output', output.value]
    if expression:
        args += ['--expression', expression]
    if module:
        args += ['--module', module]
    if sort:
        args += ['--sort', sort]
    if gen_glr_parser:
        args += ['--gen-glr-parser']
    return args


class KPrint:
    definition_dir: Path
    use_directory: Path | None
    main_module: str
    backend: str
    _extra_unparsing_modules: Iterable[KFlatModule]
    _patch_symbol_table: Callable[[SymbolTable], None] | None

    _bug_report: BugReport | None

    def __init__(
        self,
        definition_dir: Path,
        use_directory: Path | None = None,
        bug_report: BugReport | None = None,
        extra_unparsing_modules: Iterable[KFlatModule] = (),
        patch_symbol_table: Callable[[SymbolTable], None] | None = None,
    ) -> None:
        self.definition_dir = definition_dir

        if use_directory:
            check_dir_path(use_directory)

        self.use_directory = use_directory
        self._definition = None
        self._symbol_table = None
        with open(self.definition_dir / 'mainModule.txt') as mm:
            self.main_module = mm.read()
        with open(self.definition_dir / 'backend.txt') as ba:
            self.backend = ba.read()
        self._extra_unparsing_modules = extra_unparsing_modules
        self._patch_symbol_table = patch_symbol_table
        self._bug_report = bug_report
        if self._bug_report:
            self._bug_report.add_definition(self.definition_dir)

    @contextmanager
    def _temp_file(self, suffix: str | None = None) -> Iterator[_TemporaryFileWrapper]:
        with NamedTemporaryFile(
            'w',
            dir=self.use_directory,
            delete=not self.use_directory,
            suffix=suffix,
        ) as ntf:
            _LOGGER.info(f'Created temporary file: {ntf.name}')
            yield ntf

    @cached_property
    def definition(self) -> KDefinition:
        return read_kast_definition(self.definition_dir / 'compiled.json')

    @cached_property
    def kompiled_kore(self) -> KompiledKore:
        return KompiledKore(self.definition_dir)

    @property
    def definition_hash(self) -> str:
        return self.definition.hash

    def parse_token(self, ktoken: KToken, *, as_rule: bool = False) -> KInner:
        input = KAstInput('rule' if as_rule else 'program')
        proc_res = self._expression_kast(
            ktoken.token,
            input=input,
            output=KAstOutput.JSON,
            sort=ktoken.sort.name,
        )
        return kast_term(json.loads(proc_res.stdout), KInner)  # type: ignore # https://github.com/python/mypy/issues/4717

    def kore_to_pretty(self, pattern: Pattern) -> str:
        proc_res = self._expression_kast(
            pattern.text,
            input=KAstInput.KORE,
            output=KAstOutput.PRETTY,
        )
        return proc_res.stdout

    def kore_to_kast(self, kore: Pattern) -> KInner:
        _LOGGER.debug(f'kore_to_kast: {kore.text}')

        try:
            return kore_to_kast(self.definition, kore)
        except ValueError as err:
            _LOGGER.warning(err)

        _LOGGER.warning(f'Falling back to using `kast` for Kore -> Kast: {kore.text}')
        proc_res = self._expression_kast(
            kore.text,
            input=KAstInput.KORE,
            output=KAstOutput.JSON,
        )
        return kast_term(json.loads(proc_res.stdout), KInner)  # type: ignore # https://github.com/python/mypy/issues/4717

    def kast_to_kore(self, kast: KInner, sort: KSort | None = None) -> Pattern:
        try:
            return kast_to_kore(self.definition, self.kompiled_kore, kast, sort)
        except ValueError as ve:
            _LOGGER.warning(ve)

        _LOGGER.warning(f'Falling back to using `kast` for KAst -> Kore: {kast}')
        kast_json = {'format': 'KAST', 'version': 2, 'term': kast.to_dict()}
        proc_res = self._expression_kast(
            json.dumps(kast_json),
            input=KAstInput.JSON,
            output=KAstOutput.KORE,
            sort=sort.name if sort is not None else None,
        )
        return KoreParser(proc_res.stdout).pattern()

    def _add_sort_injection(self, pat: Pattern, isort: KSort, osort: KSort) -> Pattern:
        if isort == osort:
            return pat
        if isort not in self.definition.subsorts(osort):
            raise ValueError(
                f'Could not find injection from subsort to supersort {isort} -> {osort} for pattern: {pat}'
            )
        return App('inj', [SortApp('Sort' + isort.name), SortApp('Sort' + osort.name)], [pat])

    def pretty_print(self, kast: KAst, *, unalias: bool = True, sort_collections: bool = False) -> str:
        return PrettyPrinter(
            self.definition,
            extra_unparsing_modules=self._extra_unparsing_modules,
            patch_symbol_table=self._patch_symbol_table,
            unalias=unalias,
            sort_collections=sort_collections,
        ).print(kast)

    def _expression_kast(
        self,
        expression: str,
        *,
        command: str | None = None,
        input: str | KAstInput | None = None,
        output: str | KAstOutput | None = None,
        module: str | None = None,
        sort: str | None = None,
        # ---
        check: bool = True,
    ) -> CompletedProcess:
        if len(expression) < 128 * 1024:
            return _kast(
                expression=expression,
                command=command,
                definition_dir=self.definition_dir,
                input=input,
                output=output,
                module=module,
                sort=sort,
                check=check,
            )

        with self._temp_file() as ntf:
            ntf.write(expression)
            ntf.flush()

            return _kast(
                ntf.name,
                command=command,
                definition_dir=self.definition_dir,
                input=input,
                output=output,
                module=module,
                sort=sort,
                check=check,
            )
