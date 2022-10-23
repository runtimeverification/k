from pyk.kore.rpc import KoreClient, KoreServer
from pyk.ktool import KompileBackend

from ..kompiled_test import KompiledTest
from ..utils import free_port_on_host


class KoreClientTest(KompiledTest):
    KOMPILE_BACKEND = KompileBackend.HASKELL

    KORE_MODULE_NAME: str
    KORE_CLIENT_TIMEOUT = 1000

    server: KoreServer
    client: KoreClient

    def setUp(self) -> None:
        super().setUp()
        port = free_port_on_host()
        self.server = KoreServer(self.kompiled_dir, self.KORE_MODULE_NAME, port)
        self.client = KoreClient('localhost', port, timeout=self.KORE_CLIENT_TIMEOUT)

    def tearDown(self) -> None:
        self.client.close()
        self.server.close()
        super().tearDown()
