import json
from pathlib import Path

from kprove_test import KProveTest

from pyk.kast import (
    EMPTY_ATT,
    KApply,
    KAst,
    KClaim,
    KDefinition,
    KRequire,
    KVariable,
)
from pyk.kastManip import rewriteAnywhereWith


class EmitJsonSpecTest(KProveTest):
    DEFN_DIR = 'definitions/imp-verification/haskell/imp-verification-kompiled'
    MAIN_FILE_NAME = 'imp-verification.k'
    USE_DIR = '.emit-json-spec-test'
    INCLUDE_DIRS = ['k-files']
    SPEC_FILE = 'specs/imp-verification/looping-spec.json'

    def setUp(self):
        super().setUp()

        with open(self.SPEC_FILE, 'r') as spec_file:
            module = KAst.from_dict(json.load(spec_file)['term'])

        claim = extract_claims(module)[0]
        self.claim = claim.let(body=eliminate_generated_top(claim.body), att=EMPTY_ATT)
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
        spec_file = Path(self.USE_DIR) / f'{spec_name}.k'
        spec_module_name = spec_name.upper()

        self.module = self.module.let(name=spec_module_name)
        definition = KDefinition(self.module.name, [self.module], requires=[KRequire(self.MAIN_FILE_NAME)])

        with open(spec_file, 'x') as f:
            f.write(self.kprove.prettyPrint(definition))

        # When
        result = self.kprove.prove(spec_file, spec_module_name)

        # Then
        self.assertTop(result)


def extract_claims(module):
    return [claim for claim in module.sentences if type(claim) is KClaim]


def eliminate_generated_top(term):
    rule = KApply('<generatedTop>', [KVariable('CONFIG'), KVariable('_')]), KVariable('CONFIG')
    return rewriteAnywhereWith(rule, term)
