from subprocess import Popen

from pyk.kore.client import KoreClient
from pyk.ktool import KompileBackend

from ..kompiled_test import KompiledTest


class KoreClientTest(KompiledTest):
    KOMPILE_BACKEND = KompileBackend.HASKELL

    KORE_MODULE_NAME: str
    KORE_SERVER_PORT = 3000
    KORE_CLIENT_TIMEOUT = 1000

    client: KoreClient
    server: Popen

    def setUp(self) -> None:
        super().setUp()
        self.server = Popen(
            [
                'kore-rpc',
                str(self.kompiled_dir / 'definition.kore'),
                '--module',
                self.KORE_MODULE_NAME,
                '--server-port',
                str(self.KORE_SERVER_PORT),
            ]
        )
        self.client = KoreClient('localhost', self.KORE_SERVER_PORT, timeout=self.KORE_CLIENT_TIMEOUT)

    def tearDown(self) -> None:
        self.client.close()
        self.server.terminate()
        self.server.wait()
        super().tearDown()
