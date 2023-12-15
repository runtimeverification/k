from __future__ import annotations

import http.client
import json
import logging
import socket
import sys
from abc import ABC, abstractmethod
from dataclasses import dataclass
from datetime import datetime, timedelta
from enum import Enum, auto
from pathlib import Path
from signal import SIGINT
from subprocess import Popen
from time import sleep
from typing import TYPE_CHECKING, ContextManager, final

from psutil import Process

from ..ktool.kprove import KoreExecLogFormat
from ..utils import check_dir_path, check_file_path, filter_none, run_process
from .syntax import And, SortApp, kore_term

if TYPE_CHECKING:
    from collections.abc import Iterable, Mapping
    from typing import Any, ClassVar, Final, TextIO, TypeVar

    from ..utils import BugReport
    from .syntax import Module, Pattern

    ER = TypeVar('ER', bound='ExecuteResult')
    RR = TypeVar('RR', bound='RewriteResult')
    LE = TypeVar('LE', bound='LogEntry')

_LOGGER: Final = logging.getLogger(__name__)


@final
@dataclass
class JsonRpcError(Exception):
    def __init__(self, message: str, code: int, data: Any = None):
        super().__init__(message)
        self.message = message
        self.code = code
        self.data = data


class Transport(ContextManager['Transport'], ABC):
    @abstractmethod
    def request(self, req: str) -> str:
        ...

    def __enter__(self) -> Transport:
        return self

    def __exit__(self, *args: Any) -> None:
        self.close()

    @abstractmethod
    def close(self) -> None:
        ...

    @abstractmethod
    def command(self, bug_report_id: str, old_id: int, bug_report_request: str) -> list[str]:
        ...

    @abstractmethod
    def description(self) -> str:
        ...


class TransportType(Enum):
    SINGLE_SOCKET = auto()
    HTTP = auto()


@final
class SingleSocketTransport(Transport):
    _host: str
    _port: int
    _sock: socket.socket
    _file: TextIO

    def __init__(self, host: str, port: int, *, timeout: int | None = None):
        self._host = host
        self._port = port
        self._sock = self._create_connection(host, port, timeout)
        self._file = self._sock.makefile('r')

    @staticmethod
    def _create_connection(host: str, port: int, timeout: int | None) -> socket.socket:
        if timeout is not None and timeout < 0:
            raise ValueError(f'Expected nonnegative timeout value, got: {timeout}')

        _LOGGER.info(f'Connecting to host: {host}:{port}')

        timeout_datetime = datetime.now() + timedelta(milliseconds=timeout) if timeout is not None else None
        while timeout_datetime is None or datetime.now() < timeout_datetime:
            try:
                sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                sock.connect((host, port))
                _LOGGER.info(f'Connected to host: {host}:{port}')
                return sock
            except ConnectionRefusedError:
                sock.close()
                sleep(0.1)

        raise RuntimeError(f'Connection timed out: {host}:{port}')

    def close(self) -> None:
        self._file.close()
        self._sock.close()

    def command(self, bug_report_id: str, old_id: int, bug_report_request: str) -> list[str]:
        return [
            'cat',
            bug_report_request,
            '|',
            'nc',
            '-Nv',
            self._host,
            str(self._port),
            '>',
            f'rpc_{bug_report_id}/{old_id:03}_actual.json',
        ]

    def request(self, req: str) -> str:
        self._sock.sendall(req.encode())
        server_addr = self.description()
        _LOGGER.debug(f'Waiting for response from {server_addr}...')
        return self._file.readline().rstrip()

    def description(self) -> str:
        return f'{self._host}:{self._port}'


@final
class HttpTransport(Transport):
    _host: str
    _port: int
    _timeout: int | None

    def __init__(self, host: str, port: int, *, timeout: int | None = None):
        self._host = host
        self._port = port
        self._timeout = timeout

    def close(self) -> None:
        pass

    def command(self, bug_report_id: str, old_id: int, bug_report_request: str) -> list[str]:
        return [
            'curl',
            '-X',
            'POST',
            '-H',
            'Content-Type: application/json',
            '-d',
            '@' + bug_report_request,
            'http://' + self._host + ':' + str(self._port),
            '>',
            f'rpc_{bug_report_id}/{old_id:03}_actual.json',
        ]

    def request(self, req: str) -> str:
        connection = http.client.HTTPConnection(self._host, self._port, timeout=self._timeout)
        connection.request('POST', '/', body=req, headers={'Content-Type': 'application/json'})
        server_addr = self.description()
        _LOGGER.debug(f'Waiting for response from {server_addr}...')
        response = connection.getresponse()
        if response.status != 200:
            raise JsonRpcError('Internal server error', -32603)
        return response.read().decode()

    def description(self) -> str:
        return f'{self._host}:{self._port}'


class JsonRpcClientFacade(ContextManager['JsonRpcClientFacade']):
    _JSON_RPC_VERSION: Final = '2.0'

    _clients: dict[str, list[JsonRpcClient]]
    _default_client: JsonRpcClient

    def __init__(
        self,
        default_host: str,
        default_port: int,
        default_transport: TransportType,
        dispatch: dict[str, list[tuple[str, int, TransportType]]],
        *,
        timeout: int | None = None,
        bug_report: BugReport | None = None,
        bug_report_id: str | None = None,
    ):
        client_cache = {}
        self._clients = {}
        self._default_client = JsonRpcClient(
            default_host,
            default_port,
            timeout=timeout,
            bug_report=bug_report,
            bug_report_id=bug_report_id,
            transport=default_transport,
        )
        client_cache[(default_host, default_port)] = self._default_client
        for method, servers in dispatch.items():
            for host, port, transport in servers:
                if (host, port) in client_cache:
                    self._update_clients(method, client_cache[(host, port)])
                else:
                    new_id = None if bug_report_id is None else bug_report_id + '_' + str(transport)
                    new_client = JsonRpcClient(
                        host, port, timeout=timeout, bug_report=bug_report, bug_report_id=new_id, transport=transport
                    )
                    self._update_clients(method, new_client)
                    client_cache[(host, port)] = new_client

    def _update_clients(self, method: str, client: JsonRpcClient) -> None:
        clients = self._clients.get(method, [])
        self._clients[method] = clients
        clients.append(client)

    def __enter__(self) -> JsonRpcClientFacade:
        return self

    def __exit__(self, *args: Any) -> None:
        self._default_client.__exit__(*args)
        for clients in self._clients.values():
            for client in clients:
                client.__exit__(*args)

    def close(self) -> None:
        self._default_client.close()
        for clients in self._clients.values():
            for client in clients:
                client.close()

    def request(self, method: str, **params: Any) -> dict[str, Any]:
        if method in self._clients:
            for client in self._clients[method]:
                response = client.request(method, **params)
                if 'error' in response:
                    return response
            return response
        else:
            return self._default_client.request(method, **params)


class JsonRpcClient(ContextManager['JsonRpcClient']):
    _JSON_RPC_VERSION: Final = '2.0'

    _transport: Transport
    _req_id: int
    _bug_report: BugReport | None
    _bug_report_id: str

    def __init__(
        self,
        host: str,
        port: int,
        *,
        timeout: int | None = None,
        bug_report: BugReport | None = None,
        bug_report_id: str | None = None,
        transport: TransportType = TransportType.SINGLE_SOCKET,
    ):
        if transport is TransportType.SINGLE_SOCKET:
            self._transport = SingleSocketTransport(host, port, timeout=timeout)
        elif transport is TransportType.HTTP:
            self._transport = HttpTransport(host, port, timeout=timeout)
        else:
            raise AssertionError()
        self._req_id = 1
        self._bug_report = bug_report
        self._bug_report_id = bug_report_id if bug_report_id is not None else str(id(self))

    def __enter__(self) -> JsonRpcClient:
        return self

    def __exit__(self, *args: Any) -> None:
        self._transport.__exit__(*args)

    def close(self) -> None:
        self._transport.close()

    def request(self, method: str, **params: Any) -> dict[str, Any]:
        old_id = self._req_id
        self._req_id += 1

        payload = {
            'jsonrpc': self._JSON_RPC_VERSION,
            'id': old_id,
            'method': method,
            'params': params,
        }

        server_addr = self._transport.description()
        _LOGGER.info(f'Sending request to {server_addr}: {old_id} - {method}')
        req = json.dumps(payload)
        if self._bug_report:
            bug_report_request = f'rpc_{self._bug_report_id}/{old_id:03}_request.json'
            self._bug_report.add_file_contents(req, Path(bug_report_request))
            self._bug_report.add_command(self._transport.command(self._bug_report_id, old_id, bug_report_request))

        _LOGGER.debug(f'Sending request to {server_addr}: {req}')
        resp = self._transport.request(req)
        if not resp:
            raise RuntimeError('Empty response received')
        _LOGGER.debug(f'Received response from {server_addr}: {resp}')

        if self._bug_report:
            bug_report_response = f'rpc_{self._bug_report_id}/{old_id:03}_response.json'
            self._bug_report.add_file_contents(resp, Path(bug_report_response))
            self._bug_report.add_command(
                [
                    'diff',
                    '-b',
                    '-s',
                    f'rpc_{self._bug_report_id}/{old_id:03}_actual.json',
                    f'rpc_{self._bug_report_id}/{old_id:03}_response.json',
                ]
            )

        data = json.loads(resp)
        self._check(data)
        assert data['id'] == old_id

        _LOGGER.info(f'Received response from {server_addr}: {old_id} - {method}')
        return data['result']

    @staticmethod
    def _check(response: Mapping[str, Any]) -> None:
        if 'error' not in response:
            return

        assert response['error']['code'] not in {-32700, -32600}, 'Malformed JSON-RPC request'
        raise JsonRpcError(**response['error'])


@final
@dataclass
class KoreClientError(Exception):  # TODO refine
    def __init__(self, message: str, code: int, data: Any = None):
        super().__init__(message)
        self.message = message
        self.code = code
        self.data = data


class StopReason(str, Enum):
    STUCK = 'stuck'
    DEPTH_BOUND = 'depth-bound'
    BRANCHING = 'branching'
    CUT_POINT_RULE = 'cut-point-rule'
    TERMINAL_RULE = 'terminal-rule'
    VACUOUS = 'vacuous'
    ABORTED = 'aborted'


@final
@dataclass(frozen=True)
class State:
    term: Pattern
    substitution: Pattern | None
    predicate: Pattern | None

    @staticmethod
    def from_dict(dct: Mapping[str, Any]) -> State:
        return State(
            term=kore_term(dct['term']),
            substitution=kore_term(dct['substitution']) if 'substitution' in dct else None,
            predicate=kore_term(dct['predicate']) if 'predicate' in dct else None,
        )

    @property
    def kore(self) -> Pattern:
        _kore = self.term
        if self.substitution is not None:
            _kore = And(SortApp('SortGeneratedTopCell'), (_kore, self.substitution))
        if self.predicate is not None:
            _kore = And(SortApp('SortGeneratedTopCell'), (_kore, self.predicate))
        return _kore


class RewriteResult(ABC):
    rule_id: str

    @classmethod
    def from_dict(cls: type[RR], dct: Mapping[str, Any]) -> RR:
        if dct['tag'] == 'success':
            return globals()['RewriteSuccess'].from_dict(dct)
        elif dct['tag'] == 'failure':
            return globals()['RewriteFailure'].from_dict(dct)
        else:
            raise ValueError(f"Expected {dct['tag']} as 'success'/'failure'")

    @abstractmethod
    def to_dict(self) -> dict[str, Any]:
        ...


@final
@dataclass(frozen=True)
class RewriteSuccess(RewriteResult):
    rule_id: str
    rewritten_term: Pattern | None

    @classmethod
    def from_dict(cls: type[RewriteSuccess], dct: Mapping[str, Any]) -> RewriteSuccess:
        return RewriteSuccess(
            rule_id=dct['rule-id'],
            rewritten_term=kore_term(dct['rewritten-term']) if 'rewritten-term' in dct else None,
        )

    def to_dict(self) -> dict[str, Any]:
        rewritten_term = {'rewritten-term': KoreClient._state(self.rewritten_term)} if self.rewritten_term else {}
        return {'tag': 'success', 'rule-id': self.rule_id} | rewritten_term


@final
@dataclass(frozen=True)
class RewriteFailure(RewriteResult):
    rule_id: str
    reason: str

    @classmethod
    def from_dict(cls: type[RewriteFailure], dct: Mapping[str, Any]) -> RewriteFailure:
        return RewriteFailure(
            rule_id=dct['rule-id'],
            reason=dct['reason'],
        )

    def to_dict(self) -> dict[str, Any]:
        return {'tag': 'failure', 'rule-id': self.rule_id, 'reason': self.reason}


class LogOrigin(str, Enum):
    KORE_RPC = 'kore-rpc'
    BOOSTER = 'booster'
    LLVM = 'llvm'


class LogEntry(ABC):  # noqa: B024
    origin: LogOrigin
    result: RewriteResult

    @classmethod
    def from_dict(cls: type[LE], dct: Mapping[str, Any]) -> LE:
        if dct['tag'] == 'rewrite':
            return globals()['LogRewrite'].from_dict(dct)
        elif dct['tag'] == 'simplification':
            return globals()['LogSimplification'].from_dict(dct)
        else:
            raise ValueError(f"Expected {dct['tag']} as 'rewrite'/'simplification'")

    @abstractmethod
    def to_dict(self) -> dict[str, Any]:
        ...


@final
@dataclass(frozen=True)
class LogRewrite(LogEntry):
    origin: LogOrigin
    result: RewriteResult

    @classmethod
    def from_dict(cls: type[LogRewrite], dct: Mapping[str, Any]) -> LogRewrite:
        return LogRewrite(
            origin=LogOrigin(dct['origin']),
            result=RewriteResult.from_dict(dct['result']),
        )

    def to_dict(self) -> dict[str, Any]:
        return {'tag': 'rewrite', 'origin': self.origin.value, 'result': self.result.to_dict()}


@final
@dataclass(frozen=True)
class LogSimplification(LogEntry):
    origin: LogOrigin
    result: RewriteResult
    original_term: Pattern | None
    original_term_index: tuple[int, ...] | None

    @classmethod
    def from_dict(cls: type[LogSimplification], dct: Mapping[str, Any]) -> LogSimplification:
        return LogSimplification(
            origin=LogOrigin(dct['origin']),
            result=RewriteResult.from_dict(dct['result']),
            original_term=kore_term(dct['original-term']) if 'original-term' in dct else None,
            original_term_index=None,  # TODO fixme
        )

    def to_dict(self) -> dict[str, Any]:
        original_term = {'original-term': KoreClient._state(self.original_term)} if self.original_term else {}
        return {'tag': 'simplification', 'origin': self.origin.value, 'result': self.result.to_dict()} | original_term


class ExecuteResult(ABC):  # noqa: B024
    _TYPES: Mapping[StopReason, str] = {
        StopReason.STUCK: 'StuckResult',
        StopReason.DEPTH_BOUND: 'DepthBoundResult',
        StopReason.BRANCHING: 'BranchingResult',
        StopReason.CUT_POINT_RULE: 'CutPointResult',
        StopReason.TERMINAL_RULE: 'TerminalResult',
        StopReason.VACUOUS: 'VacuousResult',
        StopReason.ABORTED: 'AbortedResult',
    }

    reason: ClassVar[StopReason]

    state: State
    depth: int
    next_states: tuple[State, ...] | None
    rule: str | None
    logs: tuple[LogEntry, ...]

    @classmethod
    def from_dict(cls: type[ER], dct: Mapping[str, Any]) -> ER:
        return globals()[ExecuteResult._TYPES[StopReason(dct['reason'])]].from_dict(dct)  # type: ignore

    @classmethod
    def _check_reason(cls: type[ER], dct: Mapping[str, Any]) -> None:
        reason = StopReason(dct['reason'])
        if reason is not cls.reason:
            raise AssertionError(f"Expected {cls.reason} as 'reason', found: {reason}")


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
    logs: tuple[LogEntry, ...]

    @classmethod
    def from_dict(cls: type[StuckResult], dct: Mapping[str, Any]) -> StuckResult:
        cls._check_reason(dct)
        logs = tuple(LogEntry.from_dict(l) for l in dct['logs']) if 'logs' in dct else ()
        return StuckResult(
            state=State.from_dict(dct['state']),
            depth=dct['depth'],
            logs=logs,
        )


@final
@dataclass(frozen=True)
class DepthBoundResult(ExecuteResult):
    reason = StopReason.DEPTH_BOUND
    next_states = None
    rule = None

    state: State
    depth: int
    logs: tuple[LogEntry, ...]

    @classmethod
    def from_dict(cls: type[DepthBoundResult], dct: Mapping[str, Any]) -> DepthBoundResult:
        cls._check_reason(dct)
        logs = tuple(LogEntry.from_dict(l) for l in dct['logs']) if 'logs' in dct else ()
        return DepthBoundResult(
            state=State.from_dict(dct['state']),
            depth=dct['depth'],
            logs=logs,
        )


@final
@dataclass(frozen=True)
class BranchingResult(ExecuteResult):
    reason = StopReason.BRANCHING
    rule = None

    state: State
    depth: int
    next_states: tuple[State, ...]
    logs: tuple[LogEntry, ...]

    @classmethod
    def from_dict(cls: type[BranchingResult], dct: Mapping[str, Any]) -> BranchingResult:
        cls._check_reason(dct)
        logs = tuple(LogEntry.from_dict(l) for l in dct['logs']) if 'logs' in dct else ()
        return BranchingResult(
            state=State.from_dict(dct['state']),
            depth=dct['depth'],
            next_states=tuple(State.from_dict(next_state) for next_state in dct['next-states']),
            logs=logs,
        )


@final
@dataclass(frozen=True)
class CutPointResult(ExecuteResult):
    reason = StopReason.CUT_POINT_RULE

    state: State
    depth: int
    next_states: tuple[State, ...]
    rule: str
    logs: tuple[LogEntry, ...]

    @classmethod
    def from_dict(cls: type[CutPointResult], dct: Mapping[str, Any]) -> CutPointResult:
        cls._check_reason(dct)
        logs = tuple(LogEntry.from_dict(l) for l in dct['logs']) if 'logs' in dct else ()
        return CutPointResult(
            state=State.from_dict(dct['state']),
            depth=dct['depth'],
            next_states=tuple(State.from_dict(next_state) for next_state in dct['next-states']),
            rule=dct['rule'],
            logs=logs,
        )


@final
@dataclass(frozen=True)
class TerminalResult(ExecuteResult):
    reason = StopReason.TERMINAL_RULE
    next_states = None

    state: State
    depth: int
    rule: str
    logs: tuple[LogEntry, ...]

    @classmethod
    def from_dict(cls: type[TerminalResult], dct: Mapping[str, Any]) -> TerminalResult:
        cls._check_reason(dct)
        logs = tuple(LogEntry.from_dict(l) for l in dct['logs']) if 'logs' in dct else ()
        return TerminalResult(state=State.from_dict(dct['state']), depth=dct['depth'], rule=dct['rule'], logs=logs)


@final
@dataclass(frozen=True)
class VacuousResult(ExecuteResult):
    reason = StopReason.VACUOUS
    next_states = None
    rule = None

    state: State
    depth: int
    logs: tuple[LogEntry, ...]

    @classmethod
    def from_dict(cls: type[VacuousResult], dct: Mapping[str, Any]) -> VacuousResult:
        cls._check_reason(dct)
        logs = tuple(LogEntry.from_dict(l) for l in dct['logs']) if 'logs' in dct else ()
        return VacuousResult(
            state=State.from_dict(dct['state']),
            depth=dct['depth'],
            logs=logs,
        )


@final
@dataclass(frozen=True)
class AbortedResult(ExecuteResult):
    reason = StopReason.ABORTED
    next_states = None
    rule = None

    state: State
    depth: int
    unknown_predicate: Pattern | None
    logs: tuple[LogEntry, ...]

    @classmethod
    def from_dict(cls: type[AbortedResult], dct: Mapping[str, Any]) -> AbortedResult:
        cls._check_reason(dct)
        logs = tuple(LogEntry.from_dict(l) for l in dct['logs']) if 'logs' in dct else ()
        return AbortedResult(
            state=State.from_dict(dct['state']),
            depth=dct['depth'],
            unknown_predicate=kore_term(dct['unknown-predicate']) if dct.get('unknown-predicate') else None,
            logs=logs,
        )


@final
@dataclass(frozen=True)
class ImpliesResult:
    satisfiable: bool
    implication: Pattern
    substitution: Pattern | None
    predicate: Pattern | None
    logs: tuple[LogEntry, ...]

    @staticmethod
    def from_dict(dct: Mapping[str, Any]) -> ImpliesResult:
        substitution = dct.get('condition', {}).get('substitution')
        predicate = dct.get('condition', {}).get('predicate')
        logs = tuple(LogEntry.from_dict(l) for l in dct['logs']) if 'logs' in dct else ()
        return ImpliesResult(
            satisfiable=dct['satisfiable'],
            implication=kore_term(dct['implication']),
            substitution=kore_term(substitution) if substitution is not None else None,
            predicate=kore_term(predicate) if predicate is not None else None,
            logs=logs,
        )


class GetModelResult(ABC):  # noqa: B024
    @staticmethod
    def from_dict(dct: Mapping[str, Any]) -> GetModelResult:
        status = dct['satisfiable']
        match status:
            case 'Unknown':
                return UnknownResult()
            case 'Unsat':
                return UnsatResult()
            case 'Sat':
                substitution = dct.get('substitution')
                return SatResult(model=kore_term(substitution) if substitution else None)
            case _:
                raise ValueError(f'Unknown status: {status}')


@final
@dataclass(frozen=True)
class UnknownResult(GetModelResult):
    ...


@final
@dataclass(frozen=True)
class UnsatResult(GetModelResult):
    ...


@final
@dataclass(frozen=True)
class SatResult(GetModelResult):
    model: Pattern | None


class KoreClient(ContextManager['KoreClient']):
    _KORE_JSON_VERSION: Final = 1

    _client: JsonRpcClientFacade

    def __init__(
        self,
        host: str,
        port: int,
        *,
        timeout: int | None = None,
        bug_report: BugReport | None = None,
        bug_report_id: str | None = None,
        transport: TransportType = TransportType.SINGLE_SOCKET,
        dispatch: dict[str, list[tuple[str, int, TransportType]]] | None = None,
    ):
        if dispatch is None:
            dispatch = {}
        self._client = JsonRpcClientFacade(
            host,
            port,
            transport,
            timeout=timeout,
            bug_report=bug_report,
            bug_report_id=bug_report_id,
            dispatch=dispatch,
        )

    def __enter__(self) -> KoreClient:
        return self

    def __exit__(self, *args: Any) -> None:
        self._client.__exit__(*args)

    def close(self) -> None:
        self._client.close()

    def _request(self, method: str, **params: Any) -> dict[str, Any]:
        try:
            return self._client.request(method, **params)
        except JsonRpcError as err:
            assert err.code not in {-32601, -32602}, 'Malformed Kore-RPC request'
            raise KoreClientError(message=err.message, code=err.code, data=err.data) from err

    @staticmethod
    def _state(pattern: Pattern) -> dict[str, Any]:
        return {
            'format': 'KORE',
            'version': KoreClient._KORE_JSON_VERSION,
            'term': pattern.dict,
        }

    def execute(
        self,
        pattern: Pattern,
        *,
        max_depth: int | None = None,
        cut_point_rules: Iterable[str] | None = None,
        terminal_rules: Iterable[str] | None = None,
        module_name: str | None = None,
        log_successful_rewrites: bool | None = None,
        log_failed_rewrites: bool | None = None,
        log_successful_simplifications: bool | None = None,
        log_failed_simplifications: bool | None = None,
    ) -> ExecuteResult:
        params = filter_none(
            {
                'max-depth': max_depth,
                'cut-point-rules': list(cut_point_rules) if cut_point_rules is not None else None,
                'terminal-rules': list(terminal_rules) if terminal_rules is not None else None,
                'state': self._state(pattern),
                'module': module_name,
                'log-successful-rewrites': log_successful_rewrites,
                'log-failed-rewrites': log_failed_rewrites,
                'log-successful-simplifications': log_successful_simplifications,
                'log-failed-simplifications': log_failed_simplifications,
            }
        )

        result = self._request('execute', **params)
        return ExecuteResult.from_dict(result)

    def implies(
        self,
        ant: Pattern,
        con: Pattern,
        log_successful_simplifications: bool | None = None,
        log_failed_simplifications: bool | None = None,
    ) -> ImpliesResult:
        params = filter_none(
            {
                'antecedent': self._state(ant),
                'consequent': self._state(con),
                'log-successful-simplifications': log_successful_simplifications,
                'log-failed-simplifications': log_failed_simplifications,
            }
        )

        result = self._request('implies', **params)
        return ImpliesResult.from_dict(result)

    def simplify(
        self,
        pattern: Pattern,
        log_successful_simplifications: bool | None = None,
        log_failed_simplifications: bool | None = None,
    ) -> tuple[Pattern, tuple[LogEntry, ...]]:
        params = filter_none(
            {
                'state': self._state(pattern),
                'log-successful-simplifications': log_successful_simplifications,
                'log-failed-simplifications': log_failed_simplifications,
            }
        )

        result = self._request('simplify', **params)
        logs = tuple(LogEntry.from_dict(l) for l in result['logs']) if 'logs' in result else ()
        return kore_term(result['state']), logs

    def get_model(self, pattern: Pattern, module_name: str | None = None) -> GetModelResult:
        params = filter_none(
            {
                'state': self._state(pattern),
                'module': module_name,
            }
        )

        result = self._request('get-model', **params)
        return GetModelResult.from_dict(result)

    def add_module(self, module: Module) -> str:
        result = self._request('add-module', module=module.text)
        return result['module']


class KoreServer(ContextManager['KoreServer']):
    _proc: Popen
    _pid: int
    _host: str
    _port: int

    def __init__(
        self,
        kompiled_dir: str | Path,
        module_name: str,
        *,
        port: int | None = None,
        smt_timeout: int | None = None,
        smt_retry_limit: int | None = None,
        smt_reset_interval: int | None = None,
        smt_tactic: str | None = None,
        command: str | Iterable[str] | None = None,
        bug_report: BugReport | None = None,
        haskell_log_format: KoreExecLogFormat = KoreExecLogFormat.ONELINE,
        haskell_log_entries: Iterable[str] = (),
        log_axioms_file: Path | None = None,
    ):
        kompiled_dir = Path(kompiled_dir)
        check_dir_path(kompiled_dir)

        definition_file = kompiled_dir / 'definition.kore'
        check_file_path(definition_file)

        self._check_none_or_positive(smt_timeout, 'smt_timeout')
        self._check_none_or_positive(smt_retry_limit, 'smt_retry_limit')
        self._check_none_or_positive(smt_reset_interval, 'smt_reset_interval')

        if not command:
            command = ('kore-rpc',)
        elif type(command) is str:
            command = (command,)

        args = list(command)
        args += [str(definition_file)]
        server_args = ['--module', module_name, '--server-port', str(port or 0)]
        smt_server_args = []
        if smt_timeout:
            smt_server_args += ['--smt-timeout', str(smt_timeout)]
        if smt_retry_limit:
            smt_server_args += ['--smt-retry-limit', str(smt_retry_limit)]
        if smt_reset_interval:
            smt_server_args += ['--smt-reset-interval', str(smt_reset_interval)]
        if smt_tactic:
            smt_server_args += ['--smt-tactic', smt_tactic]

        haskell_log_args = (
            [
                '--log',
                str(log_axioms_file),
                '--log-format',
                haskell_log_format.value,
                '--log-entries',
                ','.join(haskell_log_entries),
            ]
            if log_axioms_file
            else []
        )
        args += server_args
        args += smt_server_args
        args += haskell_log_args

        if bug_report:
            self._gather_server_report(
                module_name,
                list(command)[0],
                bug_report,
                definition_file,
                list(command)[1:] + smt_server_args + haskell_log_args,
            )

        _LOGGER.info(f'Starting KoreServer: {" ".join(args)}')

        self._proc = Popen(args)
        self._pid = self._proc.pid
        self._host, self._port = self._get_host_and_port(self._pid)
        if port:
            assert self.port == port
        _LOGGER.info(f'KoreServer started: {self.host}:{self.port}, pid={self.pid}')

    @staticmethod
    def _gather_server_report(
        module_name: str, prog_name: str, bug_report: BugReport, definition_file: Path, extra_args: list[str]
    ) -> None:
        bug_report.add_file(definition_file, Path('definition.kore'))
        version_info = run_process((prog_name, '--version'), pipe_stderr=True, logger=_LOGGER).stdout.strip()
        bug_report.add_file_contents(version_info, Path('server_version.txt'))
        server_instance = {
            'exe': prog_name,
            'module': module_name,
            'extra_args': extra_args,
        }
        bug_report.add_file_contents(json.dumps(server_instance), Path('server_instance.json'))

    @staticmethod
    def _check_none_or_positive(n: int | None, param_name: str) -> None:
        if n is not None and n <= 0:
            raise ValueError(f'Expected positive integer for: {param_name}, got: {n}')

    @staticmethod
    def _get_host_and_port(pid: int) -> tuple[str, int]:
        proc = Process(pid)
        while not proc.connections():
            sleep(0.01)
        conns = proc.connections()
        assert len(conns) == 1
        conn = conns[0]
        return conn.laddr

    @property
    def pid(self) -> int:
        return self._pid

    @property
    def host(self) -> str:
        return self._host

    @property
    def port(self) -> int:
        return self._port

    def __enter__(self) -> KoreServer:
        return self

    def __exit__(self, *args: Any) -> None:
        self.close()

    def close(self) -> None:
        self._proc.send_signal(SIGINT)
        self._proc.wait()
        _LOGGER.info(f'KoreServer stopped: {self.host}:{self.port}, pid={self.pid}')


class BoosterServer(KoreServer):
    def __init__(
        self,
        kompiled_dir: str | Path,
        llvm_kompiled_dir: str | Path,
        module_name: str,
        *,
        port: int | None = None,
        smt_timeout: int | None = None,
        smt_retry_limit: int | None = None,
        smt_reset_interval: int | None = None,
        smt_tactic: str | None = None,
        command: str | Iterable[str] | None,
        bug_report: BugReport | None = None,
        haskell_log_format: KoreExecLogFormat = KoreExecLogFormat.ONELINE,
        haskell_log_entries: Iterable[str] = (),
        log_axioms_file: Path | None = None,
    ):
        llvm_kompiled_dir = Path(llvm_kompiled_dir)
        check_dir_path(llvm_kompiled_dir)

        ext: str
        match sys.platform:
            case 'linux':
                ext = 'so'
            case 'darwin':
                ext = 'dylib'
            case _:
                raise ValueError('Unsupported platform: {sys.platform}')

        dylib = llvm_kompiled_dir / f'interpreter.{ext}'
        check_file_path(dylib)
        llvm_definition = llvm_kompiled_dir / 'definition.kore'
        check_file_path(llvm_definition)
        llvm_dt = llvm_kompiled_dir / 'dt'
        check_dir_path(llvm_dt)

        if bug_report:
            self._gather_booster_report(llvm_kompiled_dir, llvm_definition, llvm_dt, bug_report)

        self._check_none_or_positive(smt_timeout, 'smt_timeout')
        self._check_none_or_positive(smt_retry_limit, 'smt_retry_limit')
        self._check_none_or_positive(smt_reset_interval, 'smt_reset_interval')

        if not command:
            command = ('kore-rpc-booster',)
        elif type(command) is str:
            command = (command,)

        args = list(command)
        args += ['--llvm-backend-library', str(dylib)]
        super().__init__(
            kompiled_dir=kompiled_dir,
            module_name=module_name,
            port=port,
            smt_timeout=smt_timeout,
            smt_retry_limit=smt_retry_limit,
            smt_reset_interval=smt_reset_interval,
            smt_tactic=smt_tactic,
            command=args,
            bug_report=bug_report,
            haskell_log_format=haskell_log_format,
            haskell_log_entries=haskell_log_entries,
            log_axioms_file=log_axioms_file,
        )

    @staticmethod
    def _gather_booster_report(
        llvm_kompiled_dir: Path, llvm_definition: Path, llvm_dt: Path, bug_report: BugReport
    ) -> None:
        bug_report.add_file(llvm_definition, Path('llvm_definition/definition.kore'))
        bug_report.add_file(llvm_dt, Path('llvm_definition/dt'))
        llvm_version = run_process('llvm-backend-version', pipe_stderr=True, logger=_LOGGER).stdout.strip()
        bug_report.add_file_contents(llvm_version, Path('llvm_version.txt'))


def kore_server(
    definition_dir: str | Path,
    module_name: str,
    *,
    llvm_definition_dir: Path | None = None,
    port: int | None = None,
    command: str | Iterable[str] | None = None,
    bug_report: BugReport | None = None,
    smt_timeout: int | None = None,
    smt_retry_limit: int | None = None,
    smt_tactic: str | None = None,
    haskell_log_format: KoreExecLogFormat = KoreExecLogFormat.ONELINE,
    haskell_log_entries: Iterable[str] = (),
    log_axioms_file: Path | None = None,
) -> KoreServer:
    if llvm_definition_dir:
        return BoosterServer(
            kompiled_dir=definition_dir,
            llvm_kompiled_dir=llvm_definition_dir,
            module_name=module_name,
            port=port,
            command=command,
            bug_report=bug_report,
            smt_timeout=smt_timeout,
            smt_retry_limit=smt_retry_limit,
            smt_tactic=smt_tactic,
            haskell_log_format=haskell_log_format,
            haskell_log_entries=haskell_log_entries,
            log_axioms_file=log_axioms_file,
        )

    return KoreServer(
        kompiled_dir=definition_dir,
        module_name=module_name,
        port=port,
        command=command,
        bug_report=bug_report,
        smt_timeout=smt_timeout,
        smt_retry_limit=smt_retry_limit,
        smt_tactic=smt_tactic,
        haskell_log_format=haskell_log_format,
        haskell_log_entries=haskell_log_entries,
        log_axioms_file=log_axioms_file,
    )
