import json
import logging
import socket
from abc import ABC
from dataclasses import dataclass
from datetime import datetime, timedelta
from enum import Enum
from pathlib import Path
from subprocess import Popen
from time import sleep
from typing import (
    Any,
    ClassVar,
    ContextManager,
    Dict,
    Final,
    Iterable,
    Mapping,
    Optional,
    Sequence,
    TextIO,
    Tuple,
    Type,
    TypeVar,
    Union,
    final,
)

from ..cli_utils import BugReport, check_dir_path, check_file_path
from ..utils import filter_none
from .syntax import And, Pattern, SortApp

_LOGGER: Final = logging.getLogger(__name__)

ER = TypeVar('ER', bound='ExecuteResult')


@final
@dataclass(frozen=True)
class JsonRpcError(Exception):
    message: str
    code: int
    data: Any

    def __init__(self, message: str, code: int, data: Any):
        object.__setattr__(self, 'message', message)
        object.__setattr__(self, 'code', code)
        object.__setattr__(self, 'data', data)
        super().__init__(message)


class JsonRpcClient(ContextManager['JsonRpcClient']):
    _JSON_RPC_VERSION: Final = '2.0'

    _host: str
    _port: int
    _sock: socket.socket
    _file: TextIO
    _req_id: int

    _bug_report: Optional[BugReport]

    def __init__(self, host: str, port: int, *, timeout: Optional[int] = None, bug_report: Optional[BugReport] = None):
        if timeout is not None and timeout < 0:
            raise ValueError(f'Expected nonnegative timeout value, got: {timeout}')

        self._host = host
        self._port = port
        self._bug_report = bug_report
        self._sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self._file = self._sock.makefile('r')
        self._req_id = 1

        connected = False
        timeout_datetime = datetime.now() + timedelta(milliseconds=timeout) if timeout is not None else None

        _LOGGER.info(f'Connecting to host: {host}:{port}')
        while not connected and (timeout_datetime is None or datetime.now() < timeout_datetime):
            try:
                self._sock.connect((host, port))
                connected = True
            except BaseException:  # TODO refine
                sleep(0.1)

        if not connected:
            self.close()
            raise RuntimeError(f"Couldn't connect to host: {host}:{port}")

        _LOGGER.info(f'Connected to host: {host}:{port}')

    def __enter__(self) -> 'JsonRpcClient':
        return self

    def __exit__(self, *args: Any) -> None:
        self._file.__exit__(*args)
        self._sock.__exit__(*args)

    def close(self) -> None:
        self._file.close()
        self._sock.close()

    def request(self, method: str, **params: Any) -> Dict[str, Any]:
        old_id = self._req_id
        self._req_id += 1

        payload = {
            'jsonrpc': self._JSON_RPC_VERSION,
            'id': old_id,
            'method': method,
            'params': params,
        }

        server_addr = f'{self._host}:{self._port}'
        req = json.dumps(payload)
        if self._bug_report:
            bug_report_request = f'rpc/{old_id:03}_request.json'
            self._bug_report.add_file_contents(req, Path(bug_report_request))
            self._bug_report.add_command(
                [
                    'cat',
                    bug_report_request,
                    '|',
                    'nc',
                    '-Nv',
                    self._host,
                    str(self._port),
                    '>',
                    f'rpc/{old_id:03}_actual.json',
                ]
            )

        _LOGGER.debug(f'Sending request to {server_addr}: {req}')
        self._sock.sendall(req.encode())
        _LOGGER.debug(f'Waiting for response from {server_addr}...')
        resp = self._file.readline().rstrip()
        _LOGGER.debug(f'Received response from {server_addr}: {resp}')

        if self._bug_report:
            bug_report_response = f'rpc/{old_id:03}_response.json'
            self._bug_report.add_file_contents(resp, Path(bug_report_response))
            self._bug_report.add_command(
                ['diff', '-b', '-s', f'rpc/{old_id:03}_actual.json', f'rpc/{old_id:03}_response.json']
            )

        data = json.loads(resp)
        self._check(data)
        assert data['id'] == old_id

        return data['result']

    @staticmethod
    def _check(response: Mapping[str, Any]) -> None:
        if 'error' not in response:
            return

        assert response['error']['code'] not in {-32700, -32600}, 'Malformed JSON-RPC request'
        raise JsonRpcError(**response['error'])


@final
@dataclass(frozen=True)
class KoreClientError(Exception):
    message: str
    code: int
    context: Tuple[str, ...]

    def __init__(self, message: str, code: int, context: Sequence[str] = ()):
        object.__setattr__(self, 'message', message)
        object.__setattr__(self, 'code', code)
        object.__setattr__(self, 'context', tuple(context))
        super().__init__(message)


class StopReason(str, Enum):
    STUCK = 'stuck'
    DEPTH_BOUND = 'depth-bound'
    BRANCHING = 'branching'
    CUT_POINT_RULE = 'cut-point-rule'
    TERMINAL_RULE = 'terminal-rule'


@final
@dataclass(frozen=True)
class State:
    term: Pattern
    substitution: Optional[Pattern]
    predicate: Optional[Pattern]

    @staticmethod
    def from_dict(dct: Mapping[str, Any]) -> 'State':
        return State(
            term=Pattern.from_dict(dct['term']['term']),
            substitution=Pattern.from_dict(dct['substitution']['term']) if 'substitution' in dct else None,
            predicate=Pattern.from_dict(dct['predicate']['term']) if 'predicate' in dct else None,
        )

    @property
    def kore(self) -> Pattern:
        _kore = self.term
        if self.substitution is not None:
            _kore = And(SortApp('SortGeneratedTopCell'), _kore, self.substitution)
        if self.predicate is not None:
            _kore = And(SortApp('SortGeneratedTopCell'), _kore, self.predicate)
        return _kore


class ExecuteResult(ABC):  # noqa: B024
    _TYPES: Mapping[StopReason, str] = {
        StopReason.STUCK: 'StuckResult',
        StopReason.DEPTH_BOUND: 'DepthBoundResult',
        StopReason.BRANCHING: 'BranchingResult',
        StopReason.CUT_POINT_RULE: 'CutPointResult',
        StopReason.TERMINAL_RULE: 'TerminalResult',
    }

    reason: ClassVar[StopReason]

    state: State
    depth: int
    next_states: Optional[Tuple[State, ...]]
    rule: Optional[str]

    @classmethod
    def from_dict(cls: Type[ER], dct: Mapping[str, Any]) -> ER:
        return globals()[ExecuteResult._TYPES[StopReason(dct['reason'])]].from_dict(dct)  # type: ignore

    @classmethod
    def _check_reason(cls: Type[ER], dct: Mapping[str, Any]) -> None:
        reason = StopReason(dct['reason'])
        if reason is not cls.reason:
            raise ValueError(f"Expected {cls.reason} as 'reason', found: {reason}")


@final
@dataclass(frozen=True)
class StuckResult(ExecuteResult):
    # These fields should be Final, but it makes mypy crash
    # https://github.com/python/mypy/issues/10090
    reason = StopReason.STUCK
    next_states = None
    rule = None

    state: State
    depth: int

    @classmethod
    def from_dict(cls: Type['StuckResult'], dct: Mapping[str, Any]) -> 'StuckResult':
        cls._check_reason(dct)
        return StuckResult(
            state=State.from_dict(dct['state']),
            depth=dct['depth'],
        )


@final
@dataclass(frozen=True)
class DepthBoundResult(ExecuteResult):
    reason = StopReason.DEPTH_BOUND
    next_states = None
    rule = None

    state: State
    depth: int

    @classmethod
    def from_dict(cls: Type['DepthBoundResult'], dct: Mapping[str, Any]) -> 'DepthBoundResult':
        cls._check_reason(dct)
        return DepthBoundResult(
            state=State.from_dict(dct['state']),
            depth=dct['depth'],
        )


@final
@dataclass(frozen=True)
class BranchingResult(ExecuteResult):
    reason = StopReason.BRANCHING
    rule = None

    state: State
    depth: int
    next_states: Tuple[State, ...]

    @classmethod
    def from_dict(cls: Type['BranchingResult'], dct: Mapping[str, Any]) -> 'BranchingResult':
        cls._check_reason(dct)
        return BranchingResult(
            state=State.from_dict(dct['state']),
            depth=dct['depth'],
            next_states=tuple(State.from_dict(next_state) for next_state in dct['next-states']),
        )


@final
@dataclass(frozen=True)
class CutPointResult(ExecuteResult):
    reason = StopReason.CUT_POINT_RULE

    state: State
    depth: int
    next_states: Tuple[State, ...]
    rule: str

    @classmethod
    def from_dict(cls: Type['CutPointResult'], dct: Mapping[str, Any]) -> 'CutPointResult':
        cls._check_reason(dct)
        return CutPointResult(
            state=State.from_dict(dct['state']),
            depth=dct['depth'],
            next_states=tuple(State.from_dict(next_state) for next_state in dct['next-states']),
            rule=dct['rule'],
        )


@final
@dataclass(frozen=True)
class TerminalResult(ExecuteResult):
    reason = StopReason.TERMINAL_RULE
    next_states = None

    state: State
    depth: int
    rule: str

    @classmethod
    def from_dict(cls: Type['TerminalResult'], dct: Mapping[str, Any]) -> 'TerminalResult':
        cls._check_reason(dct)
        return TerminalResult(
            state=State.from_dict(dct['state']),
            depth=dct['depth'],
            rule=dct['rule'],
        )


@final
@dataclass(frozen=True)
class ImpliesResult:
    satisfiable: bool
    implication: Pattern
    substitution: Optional[Pattern]
    predicate: Optional[Pattern]

    @staticmethod
    def from_dict(dct: Mapping[str, Any]) -> 'ImpliesResult':
        substitution = dct.get('condition', {}).get('substitution', {}).get('term')
        predicate = dct.get('condition', {}).get('predicate', {}).get('term')
        return ImpliesResult(
            satisfiable=dct['satisfiable'],
            implication=Pattern.from_dict(dct['implication']['term']),
            substitution=Pattern.from_dict(substitution) if substitution is not None else None,
            predicate=Pattern.from_dict(predicate) if predicate is not None else None,
        )


class KoreClient(ContextManager['KoreClient']):
    _KORE_JSON_VERSION: Final = 1

    _client: JsonRpcClient

    def __init__(self, host: str, port: int, *, timeout: Optional[int] = None, bug_report: Optional[BugReport] = None):
        self._client = JsonRpcClient(host, port, timeout=timeout, bug_report=bug_report)

    def __enter__(self) -> 'KoreClient':
        return self

    def __exit__(self, *args: Any) -> None:
        self._client.__exit__(*args)

    def close(self) -> None:
        self._client.close()

    def _request(self, method: str, **params: Any) -> Dict[str, Any]:
        try:
            return self._client.request(method, **params)
        except JsonRpcError as err:
            assert err.code not in {-32601, -32602}, 'Malformed Kore-RPC request'
            raise KoreClientError(message=err.data['error'], code=err.code, context=err.data['context']) from err

    @staticmethod
    def _state(pattern: Pattern) -> Dict[str, Any]:
        return {
            'format': 'KORE',
            'version': KoreClient._KORE_JSON_VERSION,
            'term': pattern.dict,
        }

    def execute(
        self,
        pattern: Pattern,
        *,
        max_depth: Optional[int] = None,
        cut_point_rules: Optional[Iterable[str]] = None,
        terminal_rules: Optional[Iterable[str]] = None,
    ) -> ExecuteResult:
        params = filter_none(
            {
                'max-depth': max_depth,
                'cut-point-rules': list(cut_point_rules) if cut_point_rules is not None else None,
                'terminal-rules': list(terminal_rules) if terminal_rules is not None else None,
                'state': self._state(pattern),
            }
        )

        result = self._request('execute', **params)
        return ExecuteResult.from_dict(result)

    def implies(self, ant: Pattern, con: Pattern) -> ImpliesResult:
        params = {
            'antecedent': self._state(ant),
            'consequent': self._state(con),
        }

        result = self._request('implies', **params)
        return ImpliesResult.from_dict(result)

    def simplify(self, pattern: Pattern) -> Pattern:
        params = {
            'state': self._state(pattern),
        }

        result = self._request('simplify', **params)
        return Pattern.from_dict(result['state']['term'])


class KoreServer(ContextManager['KoreServer']):
    _proc: Popen
    _port: int
    _pid: int

    def __init__(
        self,
        kompiled_dir: Union[str, Path],
        module_name: str,
        port: int,
        *,
        command: Union[str, Iterable[str]] = 'kore-rpc',
        bug_report: Optional[BugReport] = None,
    ):
        kompiled_dir = Path(kompiled_dir)
        check_dir_path(kompiled_dir)

        definition_file = kompiled_dir / 'definition.kore'
        check_file_path(definition_file)

        if type(command) is str:
            command = (command,)

        args = tuple(command) + (str(definition_file), '--module', module_name, '--server-port', str(port))

        self._port = port
        _LOGGER.info(f'Starting KoreServer: port={self._port}')
        if bug_report is not None:
            bug_report.add_command(args)
        self._proc = Popen(args)
        self._pid = self._proc.pid
        _LOGGER.info(f'KoreServer started: port={self._port}, pid={self._pid}')

    def __enter__(self) -> 'KoreServer':
        return self

    def __exit__(self, *args: Any) -> None:
        self.close()

    def close(self) -> None:
        self._proc.terminate()
        self._proc.wait()
        _LOGGER.info(f'KoreServer stopped: port={self._port}, pid={self._pid}')
