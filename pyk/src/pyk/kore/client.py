import json
import logging
import socket
from abc import ABC
from dataclasses import InitVar, dataclass
from enum import Enum
from typing import (
    Any,
    ContextManager,
    Dict,
    Final,
    Iterable,
    Iterator,
    Literal,
    Mapping,
    Optional,
    Sequence,
    TextIO,
    Tuple,
    final,
)

from ..utils import filter_none
from .syntax import Pattern

_LOGGER: Final = logging.getLogger(__name__)


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

    def __init__(self, host: str, port: int):
        self._host = host
        self._port = port
        self._sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self._file = self._sock.makefile('r')
        self._req_id = 1

        try:
            self._sock.connect((host, port))
        except BaseException:
            raise RuntimeError(f"Couldn't connect to host: {host}:{port}")

        _LOGGER.info(f'Connected to host: {host}:{port}')

    def __enter__(self) -> 'JsonRpcClient':
        return self

    def __exit__(self, *args) -> None:
        self._file.__exit__(*args)
        self._sock.__exit__(*args)

    def close(self) -> None:
        self._file.close
        self._sock.close

    def request(self, method: str, **params: Any) -> Dict[str, Any]:
        payload = {
            'jsonrpc': self._JSON_RPC_VERSION,
            'id': self._req_id,
            'method': method,
            'params': params,
        }
        old_id = self._req_id
        self._req_id += 1

        server_addr = f'{self._host}:{self._port}'
        req = json.dumps(payload)
        _LOGGER.info(f'Sending request to {server_addr}: {req}')
        self._sock.sendall(req.encode())
        _LOGGER.info(f'Waiting for response from {server_addr}...')
        resp = self._file.readline()
        _LOGGER.info(f'Received response from {server_addr}: {resp}')

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
    FINAL_STATE = 'final-state'
    STUCK = 'stuck'
    DEPTH_BOUND = 'depth-bound'
    CUT_POINT_RULE = 'cut-point-rule'
    TERMINAL_RULE = 'terminal-rule'
    BRANCHING = 'branching'


class State(ABC):
    pattern: Pattern


@final
@dataclass(frozen=True)
class DirectState(State):
    pattern: Pattern


@final
@dataclass(frozen=True)
class BranchingState(State):
    pattern: Pattern
    substitution: Pattern
    predicate: Pattern


class ExecuteResult(ABC):
    states: Tuple[State, ...]
    depth: int
    reason: StopReason

    @staticmethod
    def from_dict(dct: Mapping[str, Any]) -> 'ExecuteResult':
        if dct['reason'] is StopReason.BRANCHING:
            return BranchingResult.from_dict(dct)

        return DirectResult.from_dict(dct)


@final
@dataclass(frozen=True)
class DirectResult(ExecuteResult):
    state: DirectState
    depth: int
    reason: StopReason

    states: InitVar[Tuple[DirectState]]

    def __init__(self, state: DirectState, depth: int, reason: StopReason):
        if reason is StopReason.BRANCHING:
            raise ValueError(f'Illegal value for reason: {reason}')

        object.__setattr__(self, 'state', state)
        object.__setattr__(self, 'depth', depth)
        object.__setattr__(self, 'reason', reason)
        object.__setattr__(self, 'states', (state,))

    @staticmethod
    def from_dict(dct: Mapping[str, Any]) -> 'DirectResult':
        reason = StopReason(dct['reason'])

        state_list = dct['states']
        if len(state_list) != 1:
            raise ValueError('Expected states to be a single-element sequence')
        depth = state_list[0]['depth']
        state = DirectState(Pattern.from_dict(state_list[0]['state']['term']))

        return DirectResult(state=state, depth=depth, reason=reason)


@final
@dataclass(frozen=True)
class BranchingResult(ExecuteResult, Iterable[BranchingState]):
    states: Tuple[BranchingState, ...]
    depth: int

    reason: InitVar[Literal[StopReason.BRANCHING]]

    def __init__(self, states: Iterable[BranchingState], depth: int):
        object.__setattr__(self, 'states', tuple(states))
        object.__setattr__(self, 'depth', depth)
        object.__setattr__(self, 'reason', StopReason.BRANCHING)

    def __iter__(self) -> Iterator[BranchingState]:
        return iter(self.states)

    @staticmethod
    def from_dict(dct: Mapping[str, Any]) -> 'BranchingResult':
        reason = StopReason(dct['reason'])
        if reason is not StopReason.BRANCHING:
            raise ValueError(f'Expected {StopReason.BRANCHING} as reason value, found: {reason}')

        state_list = dct['states']
        if not state_list:
            raise ValueError('Expected states to be nonempty')

        assert all(state['depth'] == state_list[0]['depth'] for state in state_list)
        depth = state_list[0]['depth']

        states = (
            BranchingState(
                pattern=Pattern.from_dict(state['term']),
                substitution=Pattern.from_dict(state['condition']['substitution']),
                predicate=Pattern.from_dict(state['condition']['predicate']),
            )
            for state in state_list
        )

        return BranchingResult(states=states, depth=depth)


class KoreClient(ContextManager['KoreClient']):
    _KORE_JSON_VERSION: Final = 1

    _client: JsonRpcClient

    def __init__(self, host: str, port: int):
        self._client = JsonRpcClient(host, port)

    def __enter__(self):
        return self

    def __exit__(self, *args):
        self._client.__exit__(*args)

    def close(self) -> None:
        self._client.close()

    def _request(self, method: str, **params: Any) -> Dict[str, Any]:
        try:
            return self._client.request(method, **params)
        except JsonRpcError as e:
            assert e.code not in {-32601, -32602}, 'Malformed Kore-RPC request'
            raise KoreClientError(message=e.data['error'], code=e.code, context=e.data['context'])

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

    def implies(self, ant: Pattern, con: Pattern) -> Tuple[bool, Optional[Pattern], Optional[Pattern]]:
        params = {
            'antecedent': self._state(ant),
            'consequent': self._state(con),
        }

        result = self._request('implies', **params)
        satisfiable = result['satisfiable']
        substitution = Pattern.from_dict(result['substitution']) if 'substitution' in result else None
        predicate = Pattern.from_dict(result['predicate']) if 'predicate' in result else None
        return satisfiable, substitution, predicate

    def simplify(self, pattern: Pattern) -> Pattern:
        params = {
            'state': self._state(pattern),
        }

        result = self._request('simplify', **params)
        return Pattern.from_dict(result['state']['term'])
