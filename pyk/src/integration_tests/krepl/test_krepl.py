import os

from pyk.krepl.rpc.client import JsonRpcClient

from .utils import KReplTest


class KReplPidTest(KReplTest):
    def test_krepl_running(self) -> None:
        self.assertPid(self._server.pid)

    def assertPid(self, pid: int) -> None:  # noqa: N802
        try:
            os.kill(pid, 0)
        except OSError:
            raise AssertionError(f'Process with PID {pid} does not exist') from None


class KReplRpcTest(KReplTest):
    def test_request(self) -> None:
        # Given
        client = JsonRpcClient(self.KREPL_PORT)
        msg = 'Hello, World!'

        # When
        response = client.echo(msg)

        # Then
        self.assertEqual(response, msg)
