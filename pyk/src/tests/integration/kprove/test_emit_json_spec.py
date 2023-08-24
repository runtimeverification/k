from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING

import pytest

from pyk.cterm import CTerm
from pyk.kast.kast import EMPTY_ATT
from pyk.kast.manip import remove_generated_cells
from pyk.kast.outer import KDefinition, KRequire
from pyk.kast.pretty import paren
from pyk.prelude.ml import mlOr
from pyk.testing import KProveTest

from ..utils import K_FILES

if TYPE_CHECKING:
    from pyk.kast.outer import KFlatModule
    from pyk.ktool.kprint import SymbolTable
    from pyk.ktool.kprove import KProve


class TestEmitJsonSpec(KProveTest):
    MAIN_FILE_NAME = 'imp-verification.k'
    KOMPILE_MAIN_FILE = K_FILES / MAIN_FILE_NAME

    @staticmethod
    def _update_symbol_table(symbol_table: SymbolTable) -> None:
        symbol_table['_+Int_'] = paren(symbol_table['_+Int_'])

    @pytest.fixture
    def spec_module(self, kprove: KProve) -> KFlatModule:
        spec_file = K_FILES / 'looping-spec.k'
        kfml = kprove.get_claim_modules(spec_file)
        module = kfml.modules[0]
        claim = module.claims[0]
        claim = claim.let(body=remove_generated_cells(claim.body), att=EMPTY_ATT)
        return module.let(sentences=(claim,))

    def test_prove_claim(self, kprove: KProve, spec_module: KFlatModule) -> None:
        # When
        result = kprove.prove_claim(spec_module.claims[0], 'looping-1')

        # Then
        assert CTerm._is_top(mlOr([res.kast for res in result]))

    def test_prove(self, kprove: KProve, spec_module: KFlatModule) -> None:
        # Given
        spec_name = 'looping-2-spec'

        assert kprove.use_directory is not None
        spec_file = kprove.use_directory / f'{spec_name}.k'

        spec_module_name = spec_name.upper()
        include_dir = Path(self.KOMPILE_MAIN_FILE).parent

        module = spec_module.let(name=spec_module_name)
        definition = KDefinition(module.name, [module], requires=[KRequire(self.MAIN_FILE_NAME)])

        spec_file.write_text(kprove.pretty_print(definition))

        # When
        result = kprove.prove(spec_file, spec_module_name=spec_module_name, args=['-I', str(include_dir)])

        # Then
        assert CTerm._is_top(mlOr([res.kast for res in result]))
