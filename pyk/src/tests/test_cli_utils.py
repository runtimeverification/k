import os
from contextlib import contextmanager
from itertools import product
from stat import ST_SIZE
from typing import Iterator
from unittest import TestCase

from pyk.cli_utils import run_process


class RunProcessTest(TestCase):
    def test_pipe(self) -> None:
        # Given
        command = ('sh', '-c', 'echo out ; >&2 echo err')
        bools = (False, True)
        stdout, stdout_writer = os.pipe()
        stderr, stderr_writer = os.pipe()

        for pipe_stdout, pipe_stderr in product(bools, bools):
            with self.subTest(pipe_stdout=pipe_stdout, pipe_stderr=pipe_stderr):
                # When
                with redirect(stdout_writer, 1), redirect(stderr_writer, 2):
                    res = run_process(command, pipe_stdout=pipe_stdout, pipe_stderr=pipe_stderr)

                # Then
                if pipe_stdout:
                    self.assertEqual(res.stdout, 'out\n')
                    self.assertEqual(os.stat(stdout)[ST_SIZE], 0)
                else:
                    self.assertIsNone(res.stdout)
                    self.assertEqual(os.read(stdout, 1024), b'out\n')

                if pipe_stderr:
                    self.assertEqual(res.stderr, 'err\n')
                    self.assertEqual(os.stat(stderr)[ST_SIZE], 0)
                else:
                    self.assertIsNone(res.stderr)
                    self.assertEqual(os.read(stderr, 1024), b'err\n')


# https://stackoverflow.com/a/47066898
@contextmanager
def redirect(new: int, fd: int) -> Iterator[None]:
    old = os.dup(fd)
    try:
        os.dup2(new, fd)
        yield
    finally:
        os.dup2(old, fd)
