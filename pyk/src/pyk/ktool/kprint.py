from __future__ import annotations

import json
import logging
from contextlib import contextmanager
from enum import Enum
from functools import cached_property
from pathlib import Path
from tempfile import NamedTemporaryFile
from typing import TYPE_CHECKING

from ..cli.utils import check_dir_path, check_file_path
from ..kast import KAst, kast_term
from ..kast.inner import KInner
from ..kast.outer import read_kast_definition
from ..kast.pretty import PrettyPrinter
from ..konvert import kast_to_kore, kore_to_kast
from ..kore.parser import KoreParser
from ..kore.syntax import App, SortApp
from ..kore.tools import PrintOutput, kore_print
from ..utils import run_process_2
from .kompile import DefinitionInfo

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable, Iterator
    from subprocess import CompletedProcess
    from tempfile import _TemporaryFileWrapper
    from typing import Final

    from ..kast.inner import KSort, KToken
    from ..kast.outer import KDefinition, KFlatModule
    from ..kast.pretty import SymbolTable
    from ..kore.syntax import Pattern
    from ..utils import BugReport

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
    temp_dir: str | Path | None = None,
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

    if temp_dir is not None:
        temp_dir = Path(temp_dir)

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
        temp_dir=temp_dir,
        gen_glr_parser=gen_glr_parser,
    )

    return run_process_2(args, logger=_LOGGER, check=check)


def gen_glr_parser(
    parser_file: str | Path,
    *,
    command: str | None = None,
    definition_dir: str | Path | None = None,
    module: str | None = None,
    sort: str | None = None,
    temp_dir: str | Path | None = None,
) -> Path:
    parser_file = Path(parser_file)
    _kast(
        file=parser_file,
        command=command,
        definition_dir=definition_dir,
        module=module,
        sort=sort,
        temp_dir=temp_dir,
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
    temp_dir: Path | None,
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
    if temp_dir:
        args += ['--temp-dir', str(temp_dir)]
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

        info = DefinitionInfo(self.definition_dir)
        self.main_module = info.main_module_name
        self.backend = info.backend.value

        self._extra_unparsing_modules = extra_unparsing_modules
        self._patch_symbol_table = patch_symbol_table
        self._bug_report = bug_report

    @contextmanager
    def _temp_file(self, prefix: str | None = None, suffix: str | None = None) -> Iterator[_TemporaryFileWrapper]:
        with NamedTemporaryFile(
            'w',
            dir=self.use_directory,
            delete=not self.use_directory,
            prefix=prefix,
            suffix=suffix,
        ) as ntf:
            _LOGGER.info(f'Created temporary file: {ntf.name}')
            yield ntf

    @cached_property
    def definition(self) -> KDefinition:
        return read_kast_definition(self.definition_dir / 'compiled.json')

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
        return KInner.from_dict(kast_term(json.loads(proc_res.stdout)))

    def kore_to_pretty(self, pattern: Pattern) -> str:
        proc_res = self._expression_kast(
            pattern.text,
            input=KAstInput.KORE,
            output=KAstOutput.PRETTY,
        )
        return proc_res.stdout

    def kore_to_kast(self, kore: Pattern) -> KInner:
        try:
            _LOGGER.info('Invoking kore_to_kast')
            return kore_to_kast(self.definition, kore)
        except ValueError as err:
            _LOGGER.warning(err)

        _LOGGER.warning(f'Falling back to using `kore-print` for Kore -> Kast: {kore.text}')
        return KInner.from_dict(
            kast_term(json.loads(kore_print(kore, definition_dir=self.definition_dir, output=PrintOutput.JSON)))
        )

    def kast_to_kore(self, kast: KInner, sort: KSort | None = None, *, force_kast: bool = False) -> Pattern:
        if not force_kast:
            try:
                _LOGGER.info('Invoking kast_to_kore')
                return kast_to_kore(self.definition, kast, sort)
            except ValueError as ve:
                _LOGGER.warning(ve)

        _LOGGER.warning(f'Falling back to using `kast` for KAst -> Kore: {kast}')
        kast_json = {'format': 'KAST', 'version': KAst.version(), 'term': kast.to_dict()}
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

    def pretty_print(
        self, kast: KAst, *, in_module: str | None = None, unalias: bool = True, sort_collections: bool = False
    ) -> str:
        defn = self.definition.let(main_module_name=in_module)

        return PrettyPrinter(
            defn,
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
                temp_dir=self.use_directory,
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
                temp_dir=self.use_directory,
                check=check,
            )
