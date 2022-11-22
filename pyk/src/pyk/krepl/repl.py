from abc import ABC, abstractmethod
from argparse import ArgumentParser, Namespace
from dataclasses import dataclass
from functools import cached_property
from pathlib import Path
from typing import Any, Final, Generic, Iterator, Optional, Tuple, TypeVar, final

from cmd2 import Cmd, with_argparser, with_category

from ..cli_utils import check_dir_path, check_file_path, file_path
from ..kore.parser import KoreParser
from ..kore.syntax import Pattern
from ..ktool.kprint import KAstInput, KAstOutput, _kast
from ..ktool.krun import KRun, KRunOutput, _krun

T = TypeVar('T')


class Interpreter(Generic[T], ABC):
    def __iter__(self) -> Iterator[T]:
        state = self.init_state()
        while True:
            yield state
            state = self.next_state(state)

    @abstractmethod
    def init_state(self) -> T:
        ...

    @abstractmethod
    def next_state(self, state: T, steps: Optional[int] = None) -> T:
        ...


@final
@dataclass(frozen=True)
class KState:
    definition_dir: Path
    pattern: Pattern

    def __init__(self, definition_dir: Path, pattern: Pattern):
        definition_dir = definition_dir.resolve()
        check_dir_path(definition_dir)
        object.__setattr__(self, 'pattern', pattern)
        object.__setattr__(self, 'definition_dir', definition_dir)

    @cached_property
    def pretty(self) -> str:
        proc_res = _kast(
            definition_dir=self.definition_dir,
            input=KAstInput.KORE,
            output=KAstOutput.PRETTY,
            expression=self.pattern.text,
        )
        return proc_res.stdout

    def __str__(self) -> str:
        return self.pretty


class KInterpreter(Interpreter[KState]):
    definition_dir: Path
    program_file: Path

    def __init__(self, definition_dir: Path, program_file: Path) -> None:
        check_dir_path(definition_dir)
        check_file_path(program_file)
        self.definition_dir = definition_dir
        self.program_file = program_file

    def init_state(self) -> KState:
        try:
            proc_res = _krun(
                input_file=self.program_file,
                definition_dir=self.definition_dir,
                output=KRunOutput.KORE,
                depth=0,
            )
        except RuntimeError as err:
            raise ReplError('Failed to load program') from err

        pattern = KoreParser(proc_res.stdout).pattern()
        return KState(self.definition_dir, pattern)

    def next_state(self, state: KState, steps: Optional[int] = None) -> KState:
        pattern = KRun(self.definition_dir).run_kore_term(state.pattern, depth=steps)
        return KState(self.definition_dir, pattern)


def _step_parser() -> ArgumentParser:
    parser = ArgumentParser(description='Execute steps in the program')
    parser.add_argument('steps', type=int, nargs='?', default=1, metavar='STEPS', help='number of steps to take')
    return parser


def _show_parser() -> ArgumentParser:
    return ArgumentParser(description='Show the current configuration')


class ReplError(Exception):
    ...


class BaseRepl(Cmd, Generic[T], ABC):
    CAT_DEBUG: Final = 'Debugger Commands'
    CAT_BUILTIN: Final = 'Built-in Commands'

    prompt = '> '

    interpreter: Optional[Interpreter[T]]
    state: Optional[T]

    def __init__(self) -> None:
        super().__init__(allow_cli_args=False)
        self.default_category = self.CAT_BUILTIN

        self.interpreter = None
        self.state = None

    @abstractmethod
    def do_load(self, args: Any) -> Optional[bool]:  # Leaky abstraction - make extension mechanism more robust
        """
        Abstract method to set up the interpreter.
        Subclasses are expected to
        * decorate the method with `with_argparser` to ensure the right set of arguments is parsed;
        * instantiate an `Interpreter[T]` based on `args`, then set `self.interpreter`;
        * set `self.state` to `self.interpreter.init_state()`.
        """
        ...

    @with_argparser(_step_parser())
    @with_category(CAT_DEBUG)
    def do_step(self, args: Namespace) -> None:
        try:
            interpreter, state = self._check_state()
            self._check_steps(args.steps)
            self.state = interpreter.next_state(state, args.steps)
        except ReplError as err:
            self.poutput(err)

    @with_argparser(_show_parser())
    @with_category(CAT_DEBUG)
    def do_show(self, args: Namespace) -> None:
        try:
            _, state = self._check_state()
            self.poutput(state)
        except ReplError as err:
            self.poutput(err)

    def _check_state(self) -> Tuple[Interpreter, T]:
        if self.interpreter is None:
            raise ReplError('No program is loaded')
        assert self.state is not None
        return self.interpreter, self.state

    def _check_steps(self, steps: Optional[int] = None) -> None:
        if steps and steps < 0:
            raise ReplError('Depth should be non-negative')


def _load_parser() -> ArgumentParser:
    parser = ArgumentParser(description='Load a program')
    parser.add_argument('program', type=file_path, metavar='PROGRAM', help='program to load')
    return parser


class KRepl(BaseRepl[KState]):
    intro = 'K-REPL Shell\nType "help" or "?" for more information.'

    def __init__(self, definition_dir: Path):
        check_dir_path(definition_dir)
        super().__init__()
        self.definition_dir = definition_dir

    @with_argparser(_load_parser())
    @with_category(BaseRepl.CAT_DEBUG)
    def do_load(self, args: Namespace) -> None:
        self.interpreter = KInterpreter(self.definition_dir, args.program)
        self.state = self.interpreter.init_state()
