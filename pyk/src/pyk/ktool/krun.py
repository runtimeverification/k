import json
import logging
from enum import Enum
from logging import Logger
from pathlib import Path
from subprocess import CalledProcessError, CompletedProcess
from tempfile import NamedTemporaryFile
from typing import Final, List, Mapping, Optional

from ..cli_utils import check_dir_path, check_file_path, run_process
from ..cterm import CTerm
from ..kast.inner import KInner, KLabel, KSort
from ..kore.parser import KoreParser
from ..kore.syntax import DV, App, Pattern, SortApp, String
from .kprint import KPrint, _unmunge

_LOGGER: Final = logging.getLogger(__name__)


class KRun(KPrint):
    backend: str
    main_module: str
    command: str

    def __init__(
        self,
        definition_dir: Path,
        use_directory: Optional[Path] = None,
        profile: bool = False,
        command: str = 'krun',
    ) -> None:
        super(KRun, self).__init__(definition_dir, use_directory=use_directory, profile=profile)
        self.command = command
        with open(self.definition_dir / 'backend.txt', 'r') as ba:
            self.backend = ba.read()
        with open(self.definition_dir / 'mainModule.txt', 'r') as mm:
            self.main_module = mm.read()

    def run(
        self,
        pgm: KInner,
        *,
        config: Optional[Mapping[str, KInner]] = None,
        depth: Optional[int] = None,
        expand_macros: bool = False,
    ) -> CTerm:
        if config is not None and 'PGM' in config:
            raise ValueError('Cannot supply both pgm and config with PGM variable.')
        pmap = {k: 'cat' for k in config} if config is not None else None
        cmap = {k: self.kast_to_kore(v).text for k, v in config.items()} if config is not None else None
        with NamedTemporaryFile('w', dir=self.use_directory, delete=False) as ntf:
            ntf.write(self.pretty_print(pgm))
            ntf.flush()

            result = _krun(
                command=self.command,
                input_file=Path(ntf.name),
                definition_dir=self.definition_dir,
                output=KRunOutput.JSON,
                depth=depth,
                no_expand_macros=not expand_macros,
                profile=self._profile,
                cmap=cmap,
                pmap=pmap,
            )

        if result.returncode != 0:
            raise RuntimeError('Non-zero exit-code from krun.')

        result_kast = KInner.from_dict(json.loads(result.stdout)['term'])
        return CTerm(result_kast)

    def run_kore(
        self,
        pgm: KInner,
        *,
        sort: Optional[KSort] = None,
        depth: Optional[int] = None,
        expand_macros: bool = False,
    ) -> CTerm:
        kore_pgm = self.kast_to_kore(pgm, sort=sort)
        with NamedTemporaryFile('w', dir=self.use_directory) as ntf:
            ntf.write(kore_pgm.text)
            ntf.flush()

            result = _krun(
                command=self.command,
                input_file=Path(ntf.name),
                definition_dir=self.definition_dir,
                output=KRunOutput.KORE,
                parser='cat',
                depth=depth,
                no_expand_macros=not expand_macros,
                profile=self._profile,
            )

        if result.returncode != 0:
            raise RuntimeError('Non-zero exit-code from krun.')

        result_kore = KoreParser(result.stdout).pattern()
        result_kast = self.kore_to_kast(result_kore)
        return CTerm(result_kast)

    def run_kore_term(
        self,
        pattern: Pattern,
        *,
        depth: Optional[int] = None,
        expand_macros: bool = False,
    ) -> Pattern:
        with NamedTemporaryFile('w', dir=self.use_directory) as f:
            f.write(pattern.text)
            f.flush()

            proc_res = _krun(
                command=self.command,
                input_file=Path(f.name),
                definition_dir=self.definition_dir,
                output=KRunOutput.KORE,
                parser='cat',
                term=True,
                depth=depth,
                no_expand_macros=not expand_macros,
                profile=self._profile,
            )

        if proc_res.returncode != 0:
            raise RuntimeError('Non-zero exit-code from krun')

        parser = KoreParser(proc_res.stdout)
        res = parser.pattern()
        assert parser.eof
        return res

    def run_kore_config(
        self,
        config: Mapping[str, Pattern],
        *,
        depth: Optional[int] = None,
        expand_macros: bool = False,
    ) -> Pattern:
        def _config_var_token(s: str) -> DV:
            return DV(SortApp('SortKConfigVar'), String(f'${s}'))

        def _map_item(s: str, p: Pattern, sort: KSort) -> Pattern:
            _map_key = self._add_sort_injection(_config_var_token(s), KSort('KConfigVar'), KSort('KItem'))
            _map_value = self._add_sort_injection(p, sort, KSort('KItem'))
            return App("Lbl'UndsPipe'-'-GT-Unds'", [], [_map_key, _map_value])

        def _map(ps: List[Pattern]) -> Pattern:
            if len(ps) == 0:
                return App("Lbl'Stop'Map{}()", [], [])
            if len(ps) == 1:
                return ps[0]
            return App("Lbl'Unds'Map'Unds'", [], [ps[0], _map(ps[1:])])

        def _sort(p: Pattern) -> KSort:
            if type(p) is DV:
                return KSort(p.sort.name[4:])
            if type(p) is App:
                label = KLabel(_unmunge(p.symbol[3:]))
                return self.definition.return_sort(label)
            raise ValueError(f'Cannot fast-compute sort for pattern: {p}')

        config_var_map = _map([_map_item(k, v, _sort(v)) for k, v in config.items()])
        term = App('LblinitGeneratedTopCell', [], [config_var_map])

        return self.run_kore_term(term, depth=depth, expand_macros=expand_macros)


class KRunOutput(Enum):
    PRETTY = 'pretty'
    PROGRAM = 'program'
    KAST = 'kast'
    BINARY = 'binary'
    JSON = 'json'
    LATEX = 'latex'
    KORE = 'kore'
    NONE = 'none'


def _krun(
    command: str = 'krun',
    *,
    input_file: Optional[Path] = None,
    definition_dir: Optional[Path] = None,
    output: Optional[KRunOutput] = None,
    parser: Optional[str] = None,
    depth: Optional[int] = None,
    pmap: Optional[Mapping[str, str]] = None,
    cmap: Optional[Mapping[str, str]] = None,
    term: bool = False,
    no_expand_macros: bool = False,
    # ---
    check: bool = True,
    pipe_stderr: bool = False,
    logger: Optional[Logger] = None,
    profile: bool = False,
) -> CompletedProcess:
    if input_file:
        check_file_path(input_file)

    if definition_dir:
        check_dir_path(definition_dir)

    if depth and depth < 0:
        raise ValueError(f'Expected non-negative depth, got: {depth}')

    args = _build_arg_list(
        command=command,
        input_file=input_file,
        definition_dir=definition_dir,
        output=output,
        parser=parser,
        depth=depth,
        pmap=pmap,
        cmap=cmap,
        term=term,
        no_expand_macros=no_expand_macros,
    )

    try:
        return run_process(args, check=check, pipe_stderr=pipe_stderr, logger=logger or _LOGGER, profile=profile)
    except CalledProcessError as err:
        raise RuntimeError(
            f'Command krun exited with code {err.returncode} for: {input_file}', err.stdout, err.stderr
        ) from err


def _build_arg_list(
    *,
    command: str,
    input_file: Optional[Path],
    definition_dir: Optional[Path],
    output: Optional[KRunOutput],
    parser: Optional[str],
    depth: Optional[int],
    pmap: Optional[Mapping[str, str]],
    cmap: Optional[Mapping[str, str]],
    term: bool,
    no_expand_macros: bool,
) -> List[str]:
    args = [command]
    if input_file:
        args += [str(input_file)]
    if definition_dir:
        args += ['--definition', str(definition_dir)]
    if output:
        args += ['--output', output.value]
    if parser:
        args += ['--parser', parser]
    if depth is not None:
        args += ['--depth', str(depth)]
    for name, value in (pmap or {}).items():
        args += [f'-p{name}={value}']
    for name, value in (cmap or {}).items():
        args += [f'-c{name}={value}']
    if term:
        args += ['--term']
    if no_expand_macros:
        args += ['--no-expand-macros']
    return args
