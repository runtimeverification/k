from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING, final

from ..utils import run_process_2

if TYPE_CHECKING:
    from typing import Final


@final
@dataclass(frozen=True)
class KDistribution:
    """Represent the path to the K distribution.

    Attributes:
        path: Path to the K distribution.
    """

    path: Path

    @property
    def builtin_dir(self) -> Path:
        """The path to the `builtin` directory."""
        return self.path / 'include/kframework/builtin'

    @staticmethod
    def create() -> KDistribution | None:
        """Instantiate the class based on the path to the `kompile` binary."""
        kompile_bin = KDistribution._which_kompile()
        if kompile_bin is None:
            return None
        return KDistribution(kompile_bin.parents[1])

    @staticmethod
    def _which_kompile() -> Path | None:
        proc_res = run_process_2(['which', 'kompile'])
        if proc_res.returncode:
            return None
        res = Path(proc_res.stdout.rstrip())
        assert res.is_file()
        return res


K_DISTRIBUTION: Final = KDistribution.create()
