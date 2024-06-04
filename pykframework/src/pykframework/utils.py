from __future__ import annotations

import hashlib
import logging
import os
import shlex
import string
import subprocess
import sys
import tarfile
import time
from collections.abc import Hashable, Mapping
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from tempfile import NamedTemporaryFile
from typing import TYPE_CHECKING, Generic, TypeVar, cast, final, overload

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable, Iterator
    from logging import Logger
    from subprocess import CalledProcessError, CompletedProcess
    from typing import Any, Final

    P1 = TypeVar('P1')
    P2 = TypeVar('P2')
    P3 = TypeVar('P3')
    P4 = TypeVar('P4')
    Q = TypeVar('Q')
    R1 = TypeVar('R1')
    R2 = TypeVar('R2')
    R3 = TypeVar('R3')
    R4 = TypeVar('R4')
    T = TypeVar('T')
    S = TypeVar('S')

P = TypeVar('P')
R = TypeVar('R')
H = TypeVar('H', bound=Hashable)
K = TypeVar('K', bound=Hashable)
V = TypeVar('V')

_LOGGER: Final = logging.getLogger(__name__)

ROOT: Final = Path(os.path.dirname(os.path.abspath(__file__)))


# Based on: https://stackoverflow.com/a/2704866
# Perhaps one day: https://peps.python.org/pep-0603/
class FrozenDict(Mapping[K, V]):
    _dict: dict[K, V]
    _hash: int | None

    # TODO overload
    # TODO try __init__(self: FrozenDict[str, V], **kwargs: V)
    def __init__(self, *args: Any, **kwargs: Any):
        self._dict = dict(*args, **kwargs)
        self._hash = None

    def __iter__(self) -> Iterator[K]:
        return iter(self._dict)

    def __len__(self) -> int:
        return len(self._dict)

    def __getitem__(self, key: K) -> V:
        return self._dict[key]

    def __hash__(self) -> int:
        if self._hash is None:
            h = 0
            for pair in self.items():
                h ^= hash(pair)
            self._hash = h
        return self._hash

    def __str__(self) -> str:
        return f'FrozenDict({str(self._dict)})'

    def __repr__(self) -> str:
        return f'FrozenDict({repr(self._dict)})'


EMPTY_FROZEN_DICT: Final[FrozenDict] = FrozenDict()


@final
@dataclass(frozen=True)
class POSet(Generic[H]):
    image: FrozenDict[H, frozenset[H]]

    def __init__(self, relation: Iterable[tuple[H, H]]):
        _image = self._compute_image(relation)
        image: FrozenDict[H, frozenset[H]] = FrozenDict({x: frozenset(y) for x, y in _image.items()})
        object.__setattr__(self, 'image', image)

    @staticmethod
    def _compute_image(relation: Iterable[tuple[H, H]]) -> dict[H, set[H]]:
        image: dict[H, set[H]] = {}

        for x, y in relation:
            image.setdefault(x, set()).add(y)

        domain = set(image)
        for k in domain:
            for i in domain:
                if k not in image[i]:
                    continue
                for j in image[k]:
                    image[i].add(j)

        return image


def check_type(x: Any, typ: type[T]) -> T:
    if not isinstance(x, typ):
        raise ValueError(f'Expected object of type {typ.__name__}, got: {x}')
    return x


def raised(f: Callable, *args: Any, **kwargs: Any) -> BaseException | None:
    try:
        f(*args, **kwargs)
    except Exception as e:
        return e

    return None


def merge_with(f: Callable[[V, V], V], d1: Mapping[K, V], d2: Mapping[K, V]) -> dict[K, V]:
    res = dict(d1)
    for k, v2 in d2.items():
        if k in d1:
            v1 = d1[k]
            res[k] = f(v1, v2)
        else:
            res[k] = v2
    return res


def not_none(x: T | None) -> T:
    if x is None:
        raise ValueError('Expected value other than None')
    return x


def filter_none(mapping: Mapping[K, V]) -> dict[K, V]:
    return {k: v for k, v in mapping.items() if v is not None}


# Higher-order functions


class Chainable(Generic[P, R]):
    _f: Callable[[P], R]

    def __init__(self, f: Callable[[P], R]):
        self._f = f

    def __call__(self, p: P) -> R:
        return self._f(p)

    def __rshift__(self, other: Callable[[R], Q]) -> Chainable[P, Q]:
        return Chainable(lambda p: other(self(p)))


chain: Final[Chainable[Any, Any]] = Chainable(lambda x: x)


def none(x: Any) -> None:
    pass


def maybe(f: Callable[[P], R]) -> Callable[[P | None], R | None]:
    def res(p: P | None) -> R | None:
        return f(p) if p is not None else None

    return res


@overload
def tuple_of() -> Callable[[tuple[()]], tuple[()]]: ...


@overload
def tuple_of(
    f1: Callable[[P1], R1],
    /,
) -> Callable[[tuple[P1]], tuple[R1]]: ...


@overload
def tuple_of(
    f1: Callable[[P1], R1],
    f2: Callable[[P2], R2],
    /,
) -> Callable[[tuple[P1, P2]], tuple[R1, R2]]: ...


@overload
def tuple_of(
    f1: Callable[[P1], R1],
    f2: Callable[[P2], R2],
    f3: Callable[[P3], R3],
    /,
) -> Callable[[tuple[P1, P2, P3]], tuple[R1, R2, R3]]: ...


@overload
def tuple_of(
    f1: Callable[[P1], R1],
    f2: Callable[[P2], R2],
    f3: Callable[[P3], R3],
    f4: Callable[[P4], R4],
    /,
) -> Callable[[tuple[P1, P2, P3, P4]], tuple[R1, R2, R3, R4]]: ...


def tuple_of(*args: Callable) -> Callable:
    def res(t: tuple) -> tuple:
        return tuple(f(x) for f, x in zip(args, t, strict=True))

    return res


def case(
    cases: Iterable[tuple[Callable[[P], bool], Callable[[P], R]]],
    default: Callable[[P], R] | None = None,
) -> Callable[[P], R]:
    def res(p: P) -> R:
        for cond, then in cases:  # noqa: B905
            if cond(p):
                return then(p)

        if default is not None:
            return default(p)

        raise ValueError(f'No match found for: {p}')

    return res


# Iterables


def find_common_items(l1: Iterable[T], l2: Iterable[T]) -> tuple[list[T], list[T], list[T]]:
    common = []
    for i in l1:
        if i in l2:
            common.append(i)
    new_l1 = []
    new_l2 = []
    for i in l1:
        if i not in common:
            new_l1.append(i)
    for i in l2:
        if i not in common:
            new_l2.append(i)
    return (common, new_l1, new_l2)


def intersperse(iterable: Iterable[T], delimiter: T) -> Iterator[T]:
    it = iter(iterable)

    try:
        yield next(it)
    except StopIteration:
        return

    for x in it:
        yield delimiter
        yield x


def unique(iterable: Iterable[H]) -> Iterator[H]:
    elems = set()
    for elem in iterable:
        if elem in elems:
            continue
        else:
            elems.add(elem)
            yield elem


def single(iterable: Iterable[T]) -> T:
    it = iter(iterable)
    sentinel = object()

    fst = next(it, sentinel)
    if fst is sentinel:
        raise ValueError('Expected a single element, found none')
    fst = cast('T', fst)

    snd = next(it, sentinel)
    if snd is not sentinel:
        raise ValueError('Expected a single element, found more', fst, snd)

    return fst


def some(iterable: Iterable[T]) -> T | None:
    return next(iter(iterable), None)


def repeat_last(iterable: Iterable[T]) -> Iterator[T]:
    it = iter(iterable)
    last: T | None = None
    while True:
        try:
            last = next(it)
            yield last

        except StopIteration:
            if last is None:
                return

            yield last


def nonempty_str(x: Any) -> str:
    if x is None:
        raise ValueError('Expected nonempty string, found: null.')
    if type(x) is not str:
        raise TypeError('Expected nonempty string, found: {type(x)}')
    if x == '':
        raise ValueError("Expected nonempty string, found: ''")
    return x


def add_indent(indent: str, lines: Iterable[str]) -> list[str]:
    return [indent + line for line in lines]


def is_hexstring(x: str) -> bool:
    return all(c in string.hexdigits for c in x)


# Hashes


def hash_str(x: Any) -> str:
    hash = hashlib.sha256()
    hash.update(str(x).encode('utf-8'))
    return str(hash.hexdigest())


def hash_file(file: Path, chunk_num_blocks: int = 128) -> str:
    h = hashlib.sha256()
    with open(str(file), 'rb') as f:
        while chunk := f.read(chunk_num_blocks * h.block_size):
            h.update(chunk)
    return str(h.hexdigest())


def is_hash(x: Any) -> bool:
    # NB! currently only sha256 in hexdec form is detected
    # 2b9e b7c5 441e 9f7e 97f9 a4e5 fc04 a0f7 9f62 c8e9 605a ad1e 02db e8de 3c21 0422
    # 1    2    3    4    5    6    7    8    9    10   11   12   13   14   15   16
    return type(x) is str and len(x) == 64 and is_hexstring(x)


def shorten_hash(h: str, left_chars: int = 6, right_chars: int = 6) -> str:
    left = h[0:left_chars] if left_chars > 0 else ''
    right = h[-right_chars:] if right_chars > 0 else ''
    return left + '..' + right


def shorten_hashes(value: Any, left_chars: int = 6, right_chars: int = 6) -> Any:
    result: Any = None
    if is_hash(value):
        result = shorten_hash(value, left_chars, right_chars)
    elif type(value) is tuple:
        result = tuple([shorten_hashes(item) for item in value])
    elif type(value) is list:
        result = [shorten_hashes(v) for v in value]
    elif type(value) is dict:
        result = {}
        for k, v in value.items():
            result[shorten_hashes(k)] = shorten_hashes(v)
    elif type(value) is set:
        result = set()
        for item in value:
            result.add(shorten_hashes(item))
    else:
        result = value
    return result


def deconstruct_short_hash(h: str) -> tuple[str, str]:
    x = h.lower()
    if is_hash(x):
        return (x, x)
    (l, sep, r) = x.partition('..')
    if sep == '..' and is_hexstring(l) and is_hexstring(r):
        return (l, r)
    raise ValueError(f'Bad short hash: {h}')


def compare_short_hashes(lhs: str, rhs: str) -> bool:
    (l0, l1) = deconstruct_short_hash(lhs)
    (r0, r1) = deconstruct_short_hash(rhs)
    return (l0.startswith(r0) or r0.startswith(l0)) and (l1.endswith(r1) or r1.endswith(l1))


def run_process(
    args: str | Iterable[str],
    *,
    check: bool = True,
    input: str | None = None,
    pipe_stdout: bool = True,
    pipe_stderr: bool = False,
    cwd: str | Path | None = None,
    env: Mapping[str, str] | None = None,
    logger: Logger | None = None,
    exec_process: bool = False,
) -> CompletedProcess:
    if cwd is not None:
        cwd = Path(cwd)
        check_dir_path(cwd)

    if type(args) is str:
        command = args
    else:
        args = tuple(args)
        command = shlex.join(args)

    if not logger:
        logger = _LOGGER

    stdout = subprocess.PIPE if pipe_stdout else None
    stderr = subprocess.PIPE if pipe_stderr else None

    logger.info(f'Running: {command}')

    if exec_process:
        sys.stdout.flush()
        sys.stderr.flush()
        if type(args) is str:
            args = shlex.split(args)
        argslist = list(args)
        os.execvp(argslist[0], argslist)

    start_time = time.time()

    res = subprocess.run(args, input=input, cwd=cwd, env=env, stdout=stdout, stderr=stderr, text=True)

    delta_time = time.time() - start_time
    logger.info(f'Completed in {delta_time:.3f}s with status {res.returncode}: {command}')

    if check:
        res.check_returncode()

    return res


def exit_with_process_error(err: CalledProcessError) -> None:
    sys.stderr.write(f'[ERROR] Running process failed with returncode {err.returncode}:\n    {shlex.join(err.cmd)}\n')
    sys.stderr.flush()
    sys.exit(err.returncode)


def gen_file_timestamp(comment: str = '//') -> str:
    return comment + ' This file generated by: ' + sys.argv[0] + '\n' + comment + ' ' + str(datetime.now()) + '\n'


def check_dir_path(path: Path) -> None:
    path = path.resolve()
    if not path.exists():
        raise ValueError(f'Directory does not exist: {path}')
    if not path.is_dir():
        raise ValueError(f'Path is not a directory: {path}')


def check_file_path(path: Path) -> None:
    path = path.resolve()
    if not path.exists():
        raise ValueError(f'File does not exist: {path}')
    if not path.is_file():
        raise ValueError(f'Path is not a file: {path}')


def check_absolute_path(path: Path) -> None:
    if not path.is_absolute():
        raise ValueError(f'Path is not absolute: {path}')


def check_relative_path(path: Path) -> None:
    if path.is_absolute():
        raise ValueError(f'Path is not relative: {path}')


def ensure_dir_path(path: str | Path) -> Path:
    path = Path(path)
    if not path.exists():
        _LOGGER.info(f'Making directory: {path}')
        path.mkdir(parents=True, exist_ok=True)
    else:
        check_dir_path(path)
    return path


# Implementation because of outdated Python versions: https://github.com/python/cpython/blob/1de4395f62bb140563761ef5cbdf46accef3c550/Lib/pathlib.py#L554
def is_relative_to(_self: Path, other: Path) -> bool:
    return _self == other or other in _self.parents


def abs_or_rel_to(path: Path, base: Path) -> Path:
    if path.is_absolute():
        return path
    return base / path


class BugReport:
    _bug_report: Path
    _command_id: int
    _defn_id: int
    _file_remap: dict[str, str]

    def __init__(self, bug_report: Path) -> None:
        self._bug_report = bug_report.with_suffix('.tar')
        self._command_id = 0
        self._defn_id = 0
        self._file_remap = {}
        if self._bug_report.exists():
            _LOGGER.warning(f'Bug report exists, removing: {self._bug_report}')
            self._bug_report.unlink()

    def add_file(self, finput: Path, arcname: Path) -> None:
        if str(finput) not in self._file_remap:
            self._file_remap[str(finput)] = str(arcname)
            with tarfile.open(self._bug_report, 'a') as tar:
                tar.add(finput, arcname=arcname)
                _LOGGER.info(f'Added file to bug report {self._bug_report}:{arcname}: {finput}')

    def add_file_contents(self, input: str, arcname: Path) -> None:
        with NamedTemporaryFile('w') as ntf:
            ntf.write(input)
            ntf.flush()
            self.add_file(Path(ntf.name), arcname)

    def add_command(self, args: Iterable[str]) -> None:
        def _remap_arg(_a: str) -> str:
            if _a in self._file_remap:
                return self._file_remap[_a]
            _a_path = Path(_a)
            for _f in self._file_remap:
                _f_path = Path(_f)
                if is_relative_to(_a_path, _f_path):
                    return str(Path(self._file_remap[_f]) / _a_path.relative_to(_f_path))
            return _a

        remapped_args = [_remap_arg(a) for a in args]
        arcname = Path(f'commands/{self._command_id:03}.sh')
        shebang = '#!/usr/bin/env bash\nset -euxo pipefail\n'
        self.add_file_contents(shebang + ' '.join(remapped_args) + '\n', arcname)
        self._command_id += 1
