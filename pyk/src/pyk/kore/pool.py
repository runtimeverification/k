from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
from threading import current_thread
from typing import TYPE_CHECKING, ContextManager

if TYPE_CHECKING:
    from collections.abc import Callable
    from concurrent.futures import Executor, Future
    from typing import Any, Concatenate, ParamSpec, TypeVar

    from .rpc import KoreServer

    P = ParamSpec('P')
    T = TypeVar('T')


class KoreServerPool(ContextManager['KoreServerPool']):
    _create_server: Callable[[], KoreServer]
    _servers: dict[str, KoreServer]
    _executor: Executor
    _closed: bool

    def __init__(
        self,
        create_server: Callable[[], KoreServer],
        *,
        max_workers: int | None = None,
    ) -> None:
        self._create_server = create_server
        self._servers = {}
        self._executor = ThreadPoolExecutor(max_workers)
        self._closed = False

    def __enter__(self) -> KoreServerPool:
        return self

    def __exit__(self, exc_type: Any, exc_val: Any, exc_tb: Any) -> None:
        self.close()

    def close(self) -> None:
        self._executor.shutdown()
        for server in self._servers.values():
            server.close()
        self._closed = True

    def submit(self, fn: Callable[Concatenate[int, P], T], /, *args: P.args, **kwargs: P.kwargs) -> Future[T]:
        if self._closed:
            raise ValueError('KoreServerPool has been closed')
        return self._executor.submit(self._with_port(fn), *args, **kwargs)

    def _with_port(self, fn: Callable[Concatenate[int, P], T]) -> Callable[P, T]:
        def execute(*args: P.args, **kwargs: P.kwargs) -> T:
            thread_name = current_thread().name
            server = self._servers.get(thread_name)
            if server is None:
                server = self._servers.setdefault(thread_name, self._create_server())
            server_port = server.port
            return fn(server_port, *args, **kwargs)

        return execute
