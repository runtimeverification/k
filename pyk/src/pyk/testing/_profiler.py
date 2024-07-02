from __future__ import annotations

from contextlib import contextmanager
from cProfile import Profile
from pstats import SortKey, Stats
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from collections.abc import Iterable, Iterator
    from pathlib import Path


class Profiler:
    _tmp_path: Path

    def __init__(self, tmp_path: Path):
        self._tmp_path = tmp_path

    @contextmanager
    def __call__(
        self,
        file_name: str = 'profile.prof',
        *,
        sort_keys: Iterable[str | SortKey] = (),
        patterns: Iterable[str] = (),
        limit: int | float | None = None,
    ) -> Iterator[None]:
        profile_file = self._tmp_path / file_name
        _sort_keys = tuple(SortKey(key) for key in sort_keys)
        restrictions = tuple(patterns) + ((limit,) if limit is not None else ())

        with Profile() as profile:
            yield None

        with profile_file.open('w') as stream:
            stats = Stats(profile, stream=stream)
            stats.sort_stats(*_sort_keys)
            stats.print_stats(*restrictions)
