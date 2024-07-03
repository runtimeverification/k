from __future__ import annotations

import re
import shutil
from dataclasses import dataclass
from typing import ClassVar  # noqa: TC003
from typing import TYPE_CHECKING, final

from ..cli.utils import check_dir_path, check_file_path
from ..utils import run_process_2

if TYPE_CHECKING:
    from collections.abc import Iterable
    from pathlib import Path


@final
@dataclass(frozen=True)
class KVersion:
    @final
    @dataclass(frozen=True)
    class Git:
        ahead: int
        rev: str
        dirty: bool

    major: int
    minor: int
    patch: int
    git: Git | None

    _PATTERN_STR: ClassVar = (
        r'v(?P<major>[1-9]+)'
        r'\.(?P<minor>[0-9]+)'
        r'\.(?P<patch>[0-9]+)'
        r'(?P<git>'
        r'-(?P<ahead>[0-9]+)'
        r'-g(?P<rev>[0-9a-f]{10})'
        r'(?P<dirty>-dirty)?)?'
    )
    PATTERN: ClassVar = re.compile(_PATTERN_STR)

    @staticmethod
    def parse(text: str) -> KVersion:
        match = KVersion.PATTERN.fullmatch(text)
        if not match:
            raise ValueError(f'Invalid K version string: {text}')

        major = int(match['major'])
        minor = int(match['minor'])
        patch = int(match['patch'])
        git = (
            KVersion.Git(
                ahead=int(match['ahead']),
                rev=match['rev'],
                dirty=bool(match['dirty']),
            )
            if match['git']
            else None
        )

        return KVersion(major=major, minor=minor, patch=patch, git=git)

    @property
    def text(self) -> str:
        version = f'v{self.major}.{self.minor}.{self.patch}'
        dirty = '-dirty' if self.git and self.git.dirty else ''
        git = f'-{self.git.ahead}-g{self.git.rev}{dirty}' if self.git else ''
        return f'{version}{git}'


def k_version() -> KVersion:
    try:
        proc_res = run_process_2(['kompile', '--version'])
    except FileNotFoundError as err:
        raise RuntimeError('K is not installed') from err

    version = proc_res.stdout.splitlines()[0][14:]  # 'K version:    ...'
    return KVersion.parse(version)


def sync_files(source_dir: Path, target_dir: Path, file_names: Iterable[str]) -> list[Path]:
    check_dir_path(source_dir)
    shutil.rmtree(target_dir, ignore_errors=True)
    target_dir.mkdir(parents=True)

    res = []
    for file_name in file_names:
        source_file = source_dir / file_name
        check_file_path(source_file)
        target_file = target_dir / file_name
        target_file.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source_file, target_file)
        res.append(target_file)

    return res


def find_file_upwards(file_name: str, start_dir: Path) -> Path:
    check_dir_path(start_dir)
    curr_dir = start_dir.resolve()
    while True:
        path = curr_dir / file_name
        if path.is_file():
            return path
        if curr_dir == curr_dir.parent:
            raise FileNotFoundError(f'{file_name} not found')
        curr_dir = curr_dir.parent
