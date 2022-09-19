import json
from pathlib import Path

from pyk.kast import EMPTY_ATT, KAst, KDefinition, KFlatModuleList, KRequire
from pyk.kastManip import remove_generated_cells
from pyk.ktool import KompileBackend
from pyk.ktool.kprint import SymbolTable, paren
from pyk.ktool.kprove import _kprove

from .kprove_test import KProveTest


class EmitJsonSpecTest(KProveTest):
    MAIN_FILE_NAME = 'imp-verification.k'

    KOMPILE_MAIN_FILE = f'k-files/{MAIN_FILE_NAME}'
    KOMPILE_BACKEND = KompileBackend.HASKELL
    KOMPILE_OUTPUT_DIR = 'definitions/imp-verification'
    KOMPILE_EMIT_JSON = True

    KPROVE_USE_DIR = '.emit-json-spec-test'

    SPEC_FILE = 'k-files/looping-spec.k'
    SPEC_JSON_FILE = 'definitions/imp-verification/looping-spec.json'

    def setUp(self) -> None:
        super().setUp()

        spec_file = Path(self.SPEC_FILE)
        kompiled_dir = Path(self.KOMPILE_OUTPUT_DIR)
        emit_json_spec = Path(self.SPEC_JSON_FILE)
        _kprove(spec_file, kompiled_dir=kompiled_dir, emit_json_spec=emit_json_spec, dry_run=True)

        with open(self.SPEC_JSON_FILE, 'r') as f:
            kfml = KAst.from_dict(json.load(f)['term'])
            assert type(kfml) is KFlatModuleList

        module = list(kfml.modules)[0]
        claim = module.claims[0]
        self.claim = claim.let(body=remove_generated_cells(claim.body), att=EMPTY_ATT)
        self.module = module.let(sentences=(self.claim,))

    @staticmethod
    def _update_symbol_table(symbol_table: SymbolTable) -> None:
        symbol_table['_+Int_'] = paren(symbol_table['_+Int_'])

    def test_prove_claim(self) -> None:
        # When
        result = self.kprove.prove_claim(self.claim, 'looping-1')

        # Then
        self.assertTop(result)

    def test_prove(self) -> None:
        # Given
        spec_name = 'looping-2-spec'
        spec_file = Path(self.KPROVE_USE_DIR) / f'{spec_name}.k'
        spec_module_name = spec_name.upper()

        self.module = self.module.let(name=spec_module_name)
        definition = KDefinition(self.module.name, [self.module], requires=[KRequire(self.MAIN_FILE_NAME)])

        with open(spec_file, 'x') as f:
            f.write(self.kprove.pretty_print(definition))

        # When
        result = self.kprove.prove(spec_file, spec_module_name=spec_module_name)

        # Then
        self.assertTop(result)
