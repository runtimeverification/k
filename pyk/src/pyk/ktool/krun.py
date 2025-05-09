from __future__ import annotations

import logging
from enum import Enum
from os import execvp
from pathlib import Path
from shlex import join, split
from subprocess import PIPE, CalledProcessError, run
from sys import stderr, stdout
from time import time
from typing import TYPE_CHECKING

from ..cli.utils import check_dir_path, check_file_path
from ..kore.parser import KoreParser
from ..kore.tools import PrintOutput, kore_print
from ..utils import run_process, run_process_2
from .kprint import KPrint

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable, Mapping
    from logging import Logger
    from subprocess import CompletedProcess
    from typing import Final

    from ..kast.inner import KInner
    from ..kast.outer import KFlatModule
    from ..kast.pretty import SymbolTable
    from ..kore.syntax import Pattern
    from ..utils import BugReport

_LOGGER: Final = logging.getLogger(__name__)


class KRunOutput(Enum):
    PRETTY = 'pretty'
    PROGRAM = 'program'
    KAST = 'kast'
    BINARY = 'binary'
    JSON = 'json'
    LATEX = 'latex'
    KORE = 'kore'
    NONE = 'none'


class KRun(KPrint):
    command: str

    def __init__(
        self,
        definition_dir: Path,
        use_directory: Path | None = None,
        command: str = 'krun',
        bug_report: BugReport | None = None,
        extra_unparsing_modules: Iterable[KFlatModule] = (),
        patch_symbol_table: Callable[[SymbolTable], None] | None = None,
    ) -> None:
        super().__init__(
            definition_dir,
            use_directory=use_directory,
            bug_report=bug_report,
            extra_unparsing_modules=extra_unparsing_modules,
            patch_symbol_table=patch_symbol_table,
        )
        self.command = command

    def run_process(
        self,
        pgm: Pattern,
        *,
        cmap: Mapping[str, str] | None = None,
        pmap: Mapping[str, str] | None = None,
        term: bool = False,
        depth: int | None = None,
        expand_macros: bool = True,
        search_final: bool = False,
        no_pattern: bool = False,
        output: KRunOutput | None = KRunOutput.PRETTY,
        pipe_stderr: bool = True,
        bug_report: BugReport | None = None,
        debugger: bool = False,
        save_temps: bool = False,
        statistics: bool = False,
    ) -> CompletedProcess:
        with self._temp_file() as ntf:
            pgm.write(ntf)
            ntf.flush()

            return _krun(
                command=self.command,
                input_file=Path(ntf.name),
                definition_dir=self.definition_dir,
                output=KRunOutput.KORE,
                depth=depth,
                parser='cat',
                cmap=cmap,
                pmap=pmap,
                term=term,
                temp_dir=self.use_directory,
                save_temps=save_temps,
                statistics=statistics,
                no_expand_macros=not expand_macros,
                search_final=search_final,
                no_pattern=no_pattern,
                bug_report=self._bug_report,
                check=False,
                pipe_stderr=pipe_stderr,
                debugger=debugger,
            )

    def run_proof_hint(
        self,
        pgm: Pattern,
        *,
        cmap: Mapping[str, str] | None = None,
        pmap: Mapping[str, str] | None = None,
        output: KRunOutput | None = None,
        parser: str | None = None,
        term: bool = False,
        temp_dir: Path | None = None,
        save_temps: bool = False,
        statistics: bool = False,
        depth: int | None = None,
        expand_macros: bool = True,
        search_final: bool = False,
        no_pattern: bool = False,
        check: bool = False,
        pipe_stderr: bool = True,
        debugger: bool = False,
        proof_hint: bool = False,
    ) -> bytes:
        with self._temp_file() as ntf:
            pgm.write(ntf)
            ntf.flush()

            args = _build_arg_list(
                command='krun',
                input_file=Path(ntf.name),
                definition_dir=self.definition_dir,
                output=output,
                parser=parser,
                depth=depth,
                pmap=pmap,
                cmap=cmap,
                term=term,
                temp_dir=temp_dir,
                save_temps=save_temps,
                statistics=statistics,
                no_expand_macros=not expand_macros,
                search_final=search_final,
                no_pattern=no_pattern,
                debugger=debugger,
                proof_hint=proof_hint,
            )

            hints_bytes = self.__run_proof_hint_process(
                args=args, check=check, pipe_stderr=pipe_stderr, logger=_LOGGER, exec_process=debugger
            )

        return hints_bytes.stdout

    def __run_proof_hint_process(
        self,
        args: str | Iterable[str],
        *,
        check: bool = True,
        input: str | None = None,
        pipe_stdout: bool = True,
        pipe_stderr: bool = False,
        cwd: str | Path | None = None,
        logger: Logger | None = None,
        exec_process: bool = False,
    ) -> CompletedProcess:

        if cwd is not None:
            cwd = Path(cwd)
            check_dir_path(cwd)

        if type(args) is str:
            command = args
        else:
            args = tuple(args)
            command = join(args)

        if not logger:
            logger = _LOGGER

        proc_stdout = PIPE if pipe_stdout else None
        proc_stderr = PIPE if pipe_stderr else None

        logger.info(f'Running: {command}')

        if exec_process:
            stdout.flush()
            stderr.flush()
            if type(args) is str:
                args = split(args)
            argslist = list(args)
            execvp(argslist[0], argslist)

        start_time = time()

        res = run(args, input=input, cwd=cwd, stdout=proc_stdout, stderr=proc_stderr, text=False)

        delta_time = time() - start_time
        logger.info(f'Completed in {delta_time:.3f}s with status {res.returncode}: {command}')

        if check:
            res.check_returncode()

        return res

    def run(
        self,
        pgm: Pattern,
        *,
        cmap: Mapping[str, str] | None = None,
        pmap: Mapping[str, str] | None = None,
        term: bool = False,
        depth: int | None = None,
        expand_macros: bool = True,
        search_final: bool = False,
        no_pattern: bool = False,
        output: KRunOutput | None = KRunOutput.PRETTY,
        check: bool = False,
        pipe_stderr: bool = True,
        bug_report: BugReport | None = None,
        save_temps: bool = False,
        statistics: bool = False,
        debugger: bool = False,
    ) -> None:
        result = self.run_process(
            pgm,
            cmap=cmap,
            pmap=pmap,
            term=term,
            depth=depth,
            expand_macros=expand_macros,
            search_final=search_final,
            no_pattern=no_pattern,
            output=output,
            pipe_stderr=pipe_stderr,
            bug_report=bug_report,
            save_temps=save_temps,
            statistics=statistics,
            debugger=debugger,
        )

        if output != KRunOutput.NONE:
            output_kore = KoreParser(result.stdout).pattern()
            match output:
                case KRunOutput.JSON:
                    print(self.kore_to_kast(output_kore).to_json())
                case KRunOutput.KORE:
                    print(output_kore.text)
                case KRunOutput.PRETTY | KRunOutput.PROGRAM | KRunOutput.KAST | KRunOutput.BINARY | KRunOutput.LATEX:
                    print(kore_print(output_kore, definition_dir=self.definition_dir, output=PrintOutput(output.value)))
                case KRunOutput.NONE:
                    raise AssertionError()

        if check:
            result.check_returncode()

    def run_pattern(
        self,
        pattern: Pattern,
        *,
        depth: int | None = None,
        expand_macros: bool = False,
        search_final: bool = False,
        no_pattern: bool = False,
        pipe_stderr: bool = True,
        check: bool = False,
        bug_report: BugReport | None = None,
        debugger: bool = False,
    ) -> Pattern:
        proc_res = self.run_process(
            pattern,
            depth=depth,
            term=True,
            expand_macros=expand_macros,
            search_final=search_final,
            no_pattern=no_pattern,
            output=KRunOutput.NONE,
            pipe_stderr=pipe_stderr,
            bug_report=bug_report,
            debugger=debugger,
        )

        if check:
            proc_res.check_returncode()

        parser = KoreParser(proc_res.stdout)
        res = parser.pattern()
        assert parser.eof
        return res

    def krun(self, input_file: Path) -> tuple[int, KInner]:
        result = _krun(input_file=input_file, definition_dir=self.definition_dir, output=KRunOutput.KORE)
        kore = KoreParser(result.stdout).pattern()
        kast = self.kore_to_kast(kore)
        return (result.returncode, kast)


def _krun(
    command: str = 'krun',
    *,
    input_file: Path | None = None,
    definition_dir: Path | None = None,
    output: KRunOutput | None = None,
    parser: str | None = None,
    depth: int | None = None,
    cmap: Mapping[str, str] | None = None,
    pmap: Mapping[str, str] | None = None,
    term: bool = False,
    temp_dir: Path | None = None,
    save_temps: bool = False,
    statistics: bool = False,
    no_expand_macros: bool = False,
    search_final: bool = False,
    no_pattern: bool = False,
    # ---
    check: bool = True,
    pipe_stderr: bool = True,
    logger: Logger | None = None,
    bug_report: BugReport | None = None,
    debugger: bool = False,
) -> CompletedProcess:
    if input_file:
        check_file_path(input_file)

    if definition_dir:
        check_dir_path(definition_dir)

    if depth and depth < 0:
        raise ValueError(f'Expected non-negative depth, got: {depth}')

    if term and (cmap is not None or pmap is not None):
        raise ValueError('Cannot supply both term and cmap/pmap')

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
        temp_dir=temp_dir,
        save_temps=save_temps,
        statistics=statistics,
        no_expand_macros=no_expand_macros,
        search_final=search_final,
        no_pattern=no_pattern,
        debugger=debugger,
        proof_hint=False,
    )

    if bug_report is not None:
        if input_file is not None:
            new_input_file = Path(f'krun_inputs/{input_file}')
            bug_report.add_file(input_file, new_input_file)
            bug_report.add_command([a if a != str(input_file) else str(new_input_file) for a in args])
        else:
            bug_report.add_command(args)

    return run_process(args, check=check, pipe_stderr=pipe_stderr, logger=logger or _LOGGER, exec_process=debugger)


def _build_arg_list(
    *,
    command: str,
    input_file: Path | None,
    definition_dir: Path | None,
    output: KRunOutput | None,
    parser: str | None,
    depth: int | None,
    pmap: Mapping[str, str] | None,
    cmap: Mapping[str, str] | None,
    term: bool,
    temp_dir: Path | None,
    save_temps: bool,
    statistics: bool,
    no_expand_macros: bool,
    search_final: bool,
    no_pattern: bool,
    debugger: bool,
    proof_hint: bool,
) -> list[str]:
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
    if temp_dir:
        args += ['--temp-dir', str(temp_dir)]
    if save_temps:
        args += ['--save-temps']
    if statistics:
        args += ['--statistics']
    if no_expand_macros:
        args += ['--no-expand-macros']
    if search_final:
        args += ['--search-final']
    if no_pattern:
        args += ['--no-pattern']
    if debugger:
        args += ['--debugger']
    if proof_hint:
        args += ['--proof-hint']
    return args


def llvm_interpret(
    definition_dir: str | Path, pattern: Pattern, *, depth: int | None = None, check: bool = True
) -> Pattern:
    """Execute the `interpreter` binary generated by the LLVM Backend.

    Args:
        definition_dir: Path to the kompiled definition directory.
        pattern: KORE pattern to start rewriting from.
        depth: Maximal number of rewrite steps to take.

    Returns:
        The pattern resulting from the rewrites.

    Raises:
        RuntimeError: If ``check`` and the interpreter fails.
    """
    try:
        res = llvm_interpret_raw(definition_dir, pattern.text, depth=depth, check=check)
    except CalledProcessError as err:
        raise RuntimeError(f'Interpreter failed with status {err.returncode}: {err.stderr}') from err

    if not res.stdout:
        raise RuntimeError(f'Interpreter terminated with status {res.returncode} and produced no output: {res.stderr}')

    return KoreParser(res.stdout).pattern()


def llvm_interpret_raw(
    definition_dir: str | Path, kore: str, *, depth: int | None = None, check: bool = True
) -> CompletedProcess:
    """Execute the `interpreter` binary generated by the LLVM Backend, with no processing of input/output.

    Args:
        definition_dir: Path to the kompiled definition directory.
        pattern: KORE string to start rewriting from.
        depth: Maximal number of rewrite steps to take.
        check: check the return code of the CompletedProcess

    Returns:
        The CompletedProcess of the interpreter.

    Raises:
        CalledProcessError: If ``check`` and the interpreter fails.
    """
    definition_dir = Path(definition_dir)
    interpreter_file = definition_dir / 'interpreter'
    check_file_path(interpreter_file)

    depth = depth if depth is not None else -1
    args = [str(interpreter_file), '/dev/stdin', str(depth), '/dev/stdout']

    return run_process_2(args, input=kore, logger=_LOGGER, loglevel=logging.DEBUG, check=check)
