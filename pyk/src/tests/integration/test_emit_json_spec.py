import json
from pathlib import Path

import pytest

from pyk.kast.inner import EMPTY_ATT
from pyk.kast.manip import remove_generated_cells
from pyk.kast.outer import KDefinition, KFlatModule, KFlatModuleList, KRequire
from pyk.ktool.kprint import SymbolTable, paren
from pyk.ktool.kprove import KProve, _kprove
from pyk.prelude.ml import is_top

from .utils import KProveTest


class TestEmitJsonSpec(KProveTest):
    MAIN_FILE_NAME = 'imp-verification.k'
    KOMPILE_MAIN_FILE = f'k-files/{MAIN_FILE_NAME}'

    @staticmethod
    def _update_symbol_table(symbol_table: SymbolTable) -> None:
        symbol_table['_+Int_'] = paren(symbol_table['_+Int_'])

    @pytest.fixture(scope='class')
    def spec_module(self, definition_dir: Path) -> KFlatModule:
        spec_file = Path('k-files/looping-spec.k')
        spec_json_file = definition_dir / 'looping-spec.json'
        _kprove(spec_file, kompiled_dir=definition_dir, emit_json_spec=spec_json_file, dry_run=True)
        kfml = KFlatModuleList.from_dict(json.loads(spec_json_file.read_text())['term'])
        module = kfml.modules[0]
        claim = module.claims[0]
        claim = claim.let(body=remove_generated_cells(claim.body), att=EMPTY_ATT)
        return module.let(sentences=(claim,))

    def test_prove_claim(self, kprove: KProve, spec_module: KFlatModule) -> None:
        # When
        result = kprove.prove_claim(spec_module.claims[0], 'looping-1')

        # Then
        assert is_top(result)

    def test_prove(self, kprove: KProve, spec_module: KFlatModule) -> None:
        # Given
        spec_name = 'looping-2-spec'
        spec_file = kprove.use_directory / f'{spec_name}.k'
        spec_module_name = spec_name.upper()
        include_dir = Path(self.KOMPILE_MAIN_FILE).parent

        module = spec_module.let(name=spec_module_name)
        definition = KDefinition(module.name, [module], requires=[KRequire(self.MAIN_FILE_NAME)])

        spec_file.write_text(kprove.pretty_print(definition))

        # When
        result = kprove.prove(spec_file, spec_module_name=spec_module_name, args=['-I', str(include_dir)])

        # Then
        assert is_top(result)
