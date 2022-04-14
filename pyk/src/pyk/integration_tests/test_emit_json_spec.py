import json
from pathlib import Path

from ..kast import EMPTY_ATT, KAst, KDefinition, KRequire
from ..kastManip import remove_generated_cells
from ..ktool import KompileBackend, kprovex
from .kprove_test import KProveTest


class EmitJsonSpecTest(KProveTest):
    MAIN_FILE_NAME = 'imp-verification.k'

    KOMPILE_MAIN_FILE = f'k-files/{MAIN_FILE_NAME}'
    KOMPILE_BACKEND = KompileBackend.HASKELL
    KOMPILE_OUTPUT_DIR = 'definitions/imp-verification/haskell'
    KOMPILE_EMIT_JSON = True

    KPROVE_USE_DIR = '.emit-json-spec-test'

    SPEC_FILE = 'k-files/looping-spec.k'
    SPEC_JSON_FILE = 'definitions/imp-verification/haskell/looping-spec.json'

    def setUp(self):
        super().setUp()

        spec_file = Path(self.SPEC_FILE)
        directory = Path(self.KOMPILE_OUTPUT_DIR)
        emit_json_spec = Path(self.SPEC_JSON_FILE)
        kprovex(spec_file, directory=directory, emit_json_spec=emit_json_spec, dry_run=True)

        with open(self.SPEC_JSON_FILE, 'r') as spec_file:
            module = KAst.from_dict(json.load(spec_file)['term'])

        claim = module.claims[0]
        self.claim = claim.let(body=remove_generated_cells(claim.body), att=EMPTY_ATT)
        self.module = module.let(sentences=(self.claim,))

    @staticmethod
    def _update_symbol_table(symbol_table):
        def paren(f):
            def unparse(*args):
                return '(' + f(*args) + ')'
            return unparse

        symbol_table['_+Int_'] = paren(symbol_table['_+Int_'])

    def test_prove_claim(self):
        # When
        result = self.kprove.proveClaim(self.claim, 'looping-1')

        # Then
        self.assertTop(result)

    def test_prove(self):
        # Given
        spec_name = 'looping-2-spec'
        spec_file = Path(self.KPROVE_USE_DIR) / f'{spec_name}.k'
        spec_module_name = spec_name.upper()

        self.module = self.module.let(name=spec_module_name)
        definition = KDefinition(self.module.name, [self.module], requires=[KRequire(self.MAIN_FILE_NAME)])

        with open(spec_file, 'x') as f:
            f.write(self.kprove.prettyPrint(definition))

        # When
        result = self.kprove.prove(spec_file, spec_module_name)

        # Then
        self.assertTop(result)
