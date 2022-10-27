import re
from dataclasses import dataclass
from typing import ClassVar, Optional, final

from pyk.cli_utils import run_process


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
    git: Optional[Git]

    _PATTERN: ClassVar = re.compile(
        r'v(?P<major>[1-9]+)'
        r'\.(?P<minor>[0-9]+)'
        r'\.(?P<patch>[0-9]+)'
        r'(?P<git>'
        r'-(?P<ahead>[0-9]+)'
        r'-g(?P<rev>[0-9a-f]{10})'
        r'(?P<dirty>-dirty)?)?'
    )

    @staticmethod
    def parse(text: str) -> 'KVersion':
        match = KVersion._PATTERN.fullmatch(text)
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
        proc_res = run_process(['kompile', '--version'], pipe_stderr=True)
    except FileNotFoundError as err:
        raise RuntimeError('K is not installed') from err

    version = proc_res.stdout.splitlines()[0][14:]  # 'K version:    ...'
    return KVersion.parse(version)
