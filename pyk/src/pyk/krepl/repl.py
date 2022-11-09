from argparse import ArgumentParser, Namespace
from pathlib import Path
from typing import Final, Optional

from cmd2 import Cmd, with_argparser, with_category

from ..cli_utils import check_dir_path, check_file_path, file_path
from ..kore.parser import KoreParser
from ..kore.syntax import Pattern
from ..ktool.kprint import KAstInput, KAstOutput, _kast
from ..ktool.krun import KRun, KRunOutput, _krun


class DebuggerError(Exception):
    ...


class KDebugger:
    definition_dir: Path
    program_file: Optional[Path]
    pattern: Optional[Pattern]

    krun: KRun

    def __init__(self, definition_dir: Path) -> None:
        check_dir_path(definition_dir)

        self.definition_dir = definition_dir
        self.program_file = None
        self.pattern = None

        self.krun = KRun(definition_dir)

    def load(self, program_file: Path) -> None:
        check_file_path(program_file)

        try:
            proc_res = _krun(
                input_file=program_file,
                definition_dir=self.definition_dir,
                output=KRunOutput.KORE,
                depth=0,
            )
        except RuntimeError as err:
            raise DebuggerError('Failed to load program') from err

        self.pattern = KoreParser(proc_res.stdout).pattern()
        self.program_file = program_file

    def step(self, depth: int = 1) -> None:
        if self.pattern is None:
            raise DebuggerError('No loaded program')
        self.pattern = self.krun.run_kore_term(self.pattern, depth=depth)

    def show(self) -> str:
        if self.pattern is None:
            raise DebuggerError('No loded program')

        proc_res = _kast(
            definition_dir=self.definition_dir,
            input=KAstInput.KORE,
            output=KAstOutput.PRETTY,
            expression=self.pattern.text,
        )
        return proc_res.stdout


def _load_parser() -> ArgumentParser:
    parser = ArgumentParser(description='Load a program')
    parser.add_argument('program', type=file_path, metavar='PROGRAM')
    return parser


def _step_parser() -> ArgumentParser:
    parser = ArgumentParser(description='Execute a step in the program')
    parser.add_argument('depth', type=int, nargs='?', default=1, metavar='DEPTH')
    return parser


def _show_parser() -> ArgumentParser:
    return ArgumentParser(description='Show the current configuration')


class KRepl(Cmd):
    CAT_DEBUG: Final = 'Debugger Commands'
    CAT_BUILTIN: Final = 'Built-in Commands'

    intro = 'K-REPL Shell\nType "help" or "?" for more information.'
    prompt = '> '

    debugger: KDebugger

    def __init__(self, debugger: KDebugger) -> None:
        super().__init__(allow_cli_args=False)
        self.default_category = self.CAT_BUILTIN

        self.debugger = debugger

    @with_argparser(_load_parser())
    @with_category(CAT_DEBUG)
    def do_load(self, args: Namespace) -> None:
        try:
            self.debugger.load(args.program)
        except DebuggerError as err:
            self.poutput(err)

    @with_argparser(_step_parser())
    @with_category(CAT_DEBUG)
    def do_step(self, args: Namespace) -> None:
        if args.depth < 0:
            self.poutput('Depth should be non-negative')
            return

        try:
            self.debugger.step(args.depth)
        except DebuggerError as err:
            self.poutput(err)

    @with_argparser(_show_parser())
    @with_category(CAT_DEBUG)
    def do_show(self, args: Namespace) -> None:
        try:
            self.poutput(self.debugger.show())
        except DebuggerError as err:
            self.poutput(err)
