import os

from .utils import KReplTest


class ExampleKreplTest(KReplTest):
    KREPL_ARGS = ('--loglevel', 'INFO')

    def test_krepl_running(self) -> None:
        self.assertPid(self._server.pid)

    def assertPid(self, pid: int) -> None:  # noqa: N802
        try:
            os.kill(pid, 0)
        except OSError:
            raise AssertionError(f'Process with PID {pid} does not exist') from None
