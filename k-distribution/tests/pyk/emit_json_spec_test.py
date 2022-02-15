import json
from pathlib import Path

from kprove_test import KProveTest
from pyk.kast import KApply, KAtt, KClaim, KDefinition, KRequire, KRule, KToken, KVariable
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
            module = json.load(spec_file)['term']

        claim = extract_claims(module)[0]
        self.claim = KClaim(
            body=eliminate_generated_top(claim['body']),
            requires=claim['requires'],
            ensures=claim['ensures'],
            att=None
        )

        module['localSentences'] = [self.claim]
        self.module = module

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
        self.assertEqual(result['label'], '#Top')

    def test_prove(self):
        # Given
        spec_name = 'looping-2-spec'
        spec_file = Path(self.USE_DIR) / f'{spec_name}.k'
        spec_module_name = spec_name.upper()

        self.module['name'] = spec_module_name
        definition = KDefinition(self.module, [self.module], requires=[KRequire(self.MAIN_FILE_NAME)])

        with open(spec_file, 'x') as f:
            f.write(self.kprove.prettyPrint(definition))

        # When
        result = self.kprove.prove(spec_file, spec_module_name)

        # Then
        self.assertEqual(result['label'], '#Top')

    def test_prove_claim_with_lemmas(self):
        # When
        new_lemma = KRule(KToken('pred1(3) => true', 'Bool'), requires=KToken('pred1(4)', 'Bool'), att=KAtt(atts={'simplification': ''}))
        new_claim = KClaim(KToken('<k> foo => bar ... </k> <state> $n |-> 3 </state>', 'TCellFragment'), requires=KToken('pred1(4)', 'Bool'))
        result1 = self.kprove.proveClaim(new_claim, 'claim-without-lemma')
        result2 = self.kprove.proveClaim(new_claim, 'claim-with-lemma', lemmas = [new_lemma])

        # Then
        self.assertNotEqual(result1['label'], '#Top')
        self.assertEqual(result2['label'], '#Top')


def extract_claims(module):
    return [claim for claim in module['localSentences'] if claim['node'] == 'KClaim']


def eliminate_generated_top(term):
    rule = KApply('<generatedTop>', [KVariable('CONFIG'), KVariable('_')]), KVariable('CONFIG')
    return rewriteAnywhereWith(rule, term)
