from typing import Iterator, List

import pytest

from pyk.krepl_web.client import KReplClient

from ..utils import free_port_on_host, wait_for_port
from .utils import KReplServerProc


@pytest.fixture
def krepl_client() -> Iterator[KReplClient]:
    port = free_port_on_host()

    args: List[str] = []
    args += ['--host', 'localhost']
    args += ['--port', str(port)]

    with KReplServerProc(*args):
        wait_for_port(port)
        yield KReplClient('localhost', port)
