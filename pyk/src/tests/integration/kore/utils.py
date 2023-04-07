from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from pyk.kore.rpc import KoreClient, KoreServer

from ..utils import KompiledTest

if TYPE_CHECKING:
    from collections.abc import Iterator
    from pathlib import Path
    from typing import ClassVar


class KoreClientTest(KompiledTest):
    KOMPILE_BACKEND = 'haskell'

    KORE_MODULE_NAME: ClassVar[str]
    KORE_CLIENT_TIMEOUT: ClassVar = 1000

    @pytest.fixture
    def kore_client(self, definition_dir: Path) -> Iterator[KoreClient]:
        server = KoreServer(definition_dir, self.KORE_MODULE_NAME)
        client = KoreClient('localhost', server.port, timeout=self.KORE_CLIENT_TIMEOUT)
        yield client
        client.close()
        server.close()
