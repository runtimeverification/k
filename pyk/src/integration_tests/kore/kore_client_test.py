from pyk.kore.rpc import KoreClient, KoreServer
from pyk.ktool import KompileBackend

from ..kompiled_test import KompiledTest


class KoreClientTest(KompiledTest):
    KOMPILE_BACKEND = KompileBackend.HASKELL

    KORE_MODULE_NAME: str
    KORE_SERVER_PORT = 3000
    KORE_CLIENT_TIMEOUT = 1000

    server: KoreServer
    client: KoreClient

    def setUp(self) -> None:
        super().setUp()
        self.server = KoreServer(self.kompiled_dir, self.KORE_MODULE_NAME, self.KORE_SERVER_PORT)
        self.client = KoreClient('localhost', self.KORE_SERVER_PORT, timeout=self.KORE_CLIENT_TIMEOUT)

    def tearDown(self) -> None:
        self.client.close()
        self.server.close()
