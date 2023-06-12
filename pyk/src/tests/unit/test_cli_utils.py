from __future__ import annotations

import os
from contextlib import contextmanager
from stat import ST_SIZE
from typing import TYPE_CHECKING

import pytest

from pyk.utils import run_process

if TYPE_CHECKING:
    from collections.abc import Iterator


@pytest.mark.parametrize('pipe_stderr', (False, True))
@pytest.mark.parametrize('pipe_stdout', (False, True))
def test_pipe(pipe_stderr: bool, pipe_stdout: bool) -> None:
    # Given
    command = ('sh', '-c', 'echo out ; >&2 echo err')
    stdout, stdout_writer = os.pipe()
    stderr, stderr_writer = os.pipe()

    # When
    with redirect(stdout_writer, 1), redirect(stderr_writer, 2):
        res = run_process(command, pipe_stdout=pipe_stdout, pipe_stderr=pipe_stderr)

    # Then
    if pipe_stdout:
        assert res.stdout == 'out\n'
        assert os.stat(stdout)[ST_SIZE] == 0
    else:
        assert res.stdout is None
        assert os.read(stdout, 1024) == b'out\n'

    if pipe_stderr:
        assert res.stderr == 'err\n'
        assert os.stat(stderr)[ST_SIZE] == 0
    else:
        assert res.stderr is None
        assert os.read(stderr, 1024) == b'err\n'


# https://stackoverflow.com/a/47066898
@contextmanager
def redirect(new: int, fd: int) -> Iterator[None]:
    old = os.dup(fd)
    try:
        os.dup2(new, fd)
        yield
    finally:
        os.dup2(old, fd)
