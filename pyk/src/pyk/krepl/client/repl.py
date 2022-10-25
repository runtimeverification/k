from cmd import Cmd
from typing import Any, List

from pyk.cli_utils import file_path

from .client import KReplClient


class Repl(Cmd):
    intro = 'K-REPL Shell\nType "help" or "?" for more information.'
    prompt = '> '

    _client: KReplClient

    def __init__(self, host: str, port: int):
        super().__init__()
        self._client = KReplClient(host, port)

    def emptyline(self) -> bool:
        return False

    def default(self, line: str) -> Any:
        if line == 'EOF':
            return True
        return super().default(line)

    def help_help(self) -> None:
        print('Usage: help [COMMAND] - List available commands or detailed help for COMMAND')

    def do_load_raw(self, arg: str) -> None:
        """Usage: load_raw FILE - Load initial KORE pattern from FILE"""
        try:
            (arg1,) = _get_args(arg, 1)
            file_path(arg1)
        except ValueError as err:
            print(err.args[0])
            return

        print('load_raw')

    def do_step_to_branch(self, arg: str) -> None:
        """Usage: step_to_branch - Step to the next branching point"""
        try:
            _get_args(arg, 0)
        except ValueError as err:
            print(err.args[0])
            return

        print('step_branch')

    def do_exit(self, arg: str) -> bool:
        """Usage: exit - Exit REPL"""
        return True


def _get_args(s: str, n: int) -> List[str]:
    args = s.split()
    if len(args) != n:
        arg_str = '1 argument' if n == 1 else f'{n} arguments'
        raise ValueError(f'Expected {arg_str}, got: {len(args)}')
    return args
