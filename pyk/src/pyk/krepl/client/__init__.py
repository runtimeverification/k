from cmd import Cmd
from pathlib import Path
from typing import Any, Dict, Final, List, Literal, Mapping, Optional

import requests
from requests import Response

from pyk.cli_utils import check_file_path, dir_path, file_path

DEFAULT_PORT: Final = 42412


class KReplClient:
    _HOST: Final = 'localhost'

    _port: int

    def __init__(self, port: int):
        self._port = port

    def _request(self, method: Literal['GET', 'POST'], path: str, *, json: Optional[Any] = None) -> Response:
        url = f'http://{self._HOST}:{self._port}/{path}'
        response = requests.request(method, url, json=json)
        response.raise_for_status()
        return response

    def load_raw(self, path: Path) -> Dict[str, Mapping]:
        check_file_path(path)
        with open(path, 'r') as f:
            text = f.read()
        response = self._request('POST', 'load-raw', json={'term': text})
        return response.json()

    def step_to_branch(self) -> str:
        response = self._request('POST', 'step-to-branch')
        return response.json()['configId']


class Repl(Cmd):
    intro = 'K-REPL Shell\nType "help" or "?" for more information.'
    prompt = '> '

    _client: KReplClient

    def __init__(self, port: int):
        super().__init__()
        self._client = KReplClient(port)

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
            path = file_path(arg1)
        except ValueError as err:
            print(err.args[0])
            return

        try:
            response = self._client.load_raw(path)
        except Exception as err:
            print(err.args[0])
            return

        print(response)

    def do_step_to_branch(self, arg: str) -> None:
        """Usage: step_to_branch - Step to the next branching point"""
        try:
            _get_args(arg, 0)
        except ValueError as err:
            print(err.args[0])
            return

        try:
            response = self._client.step_to_branch()
        except Exception as err:
            print(err.args[0])
            return

        print(response)

    def do_exit(self, arg: str) -> bool:
        """Usage: exit - Exit REPL"""
        return True


def _get_args(s: str, n: int) -> List[str]:
    args = s.split()
    if len(args) != n:
        arg_str = '1 argument' if n == 1 else f'{n} arguments'
        raise ValueError(f'Expected {arg_str}, got: {len(args)}')
    return args
