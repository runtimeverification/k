import os

from .utils import KReplTest


class KReplPidTest(KReplTest):
    def test_krepl_running(self) -> None:
        self.assertPid(self._server.pid)

    def assertPid(self, pid: int) -> None:  # noqa: N802
        try:
            os.kill(pid, 0)
        except OSError:
            raise AssertionError(f'Process with PID {pid} does not exist') from None


class KReplRequestTest(KReplTest):
    def test_step_to_branch(self) -> None:
        # When
        response = self.client.step_to_branch()

        # Then
        self.assertEqual(response, '1')
