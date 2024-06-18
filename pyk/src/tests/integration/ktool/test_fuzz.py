from __future__ import annotations

import logging
from contextlib import nullcontext
from pathlib import Path
from typing import TYPE_CHECKING

import pytest

from pyk.cli.pyk import ProveOptions
from pyk.kast.inner import KApply, KSequence, KVariable
from pyk.kcfg.semantics import KCFGSemantics
from pyk.ktool.kprove import ProveRpc
from pyk.proof import ProofStatus
from pyk.testing import KCFGExploreTest, KompiledTest, KProveTest
from pyk.utils import single

from ..utils import K_FILES

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Final

    from pyk.cterm import CTerm
    from pyk.kast.outer import KDefinition
    from pyk.kcfg import KCFGExplore
    from pyk.kcfg.kcfg import KCFGExtendResult
    from pyk.ktool.kprove import KProve

_LOGGER: Final = logging.getLogger(__name__)

class TestImpFuzz(KompiledTest):
    KOMPILE_MAIN_FILE = K_FILES / 'imp.k'
    KOMPILE_BACKEND = 'llvm'

    def test_fuzz(definition_dir: Path):
        print(str(definition_dir))
