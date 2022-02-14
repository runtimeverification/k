import json
import os
import shutil
import unittest
from pathlib import Path

from pyk.kast import KApply, KClaim, KDefinition, KRequire, KVariable
from pyk.kastManip import rewriteAnywhereWith
from pyk.ktool import KProve


class EmitJsonSpecTest(unittest.TestCase):
    TEST_DIR = 'emit-json-spec-tests'
    MAIN_FILE = 'verification.k'
    USE_DIR = f'{TEST_DIR}/.kprove'

    def setUp(self):
        shutil.rmtree(self.USE_DIR, ignore_errors=True)
        os.makedirs(self.USE_DIR)

        self.kprove = KProve(f'{self.TEST_DIR}/verification-kompiled', self.MAIN_FILE, self.USE_DIR)
        self.kprove.proverArgs += ['-I', '.']
        self._update_symbol_table(self.kprove)

        with open(f'{self.TEST_DIR}/looping-spec.json', 'r') as spec_file:
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

    def tearDown(self):
        shutil.rmtree(self.USE_DIR)

    @staticmethod
    def _update_symbol_table(kprove):
        def paren(f):
            def unparse(*args):
                return '(' + f(*args) + ')'
            return unparse

        kprove.symbolTable['_+Int_'] = paren(kprove.symbolTable['_+Int_'])

    def test_prove_claim(self):
        # When
        result = self.kprove.proveClaim(self.claim, 'looping-1')

        # Then
        self.assertEqual(result['label'], '#Top')

    def test_prove(self):
        # Given
        spec_name = 'looping-2-spec'
        spec_path = Path(f'{self.USE_DIR}/{spec_name}.k')
        spec_module_name = spec_name.upper()

        self.module['name'] = spec_module_name
        definition = KDefinition(self.module, [self.module], requires=[KRequire(self.MAIN_FILE)])

        with open(spec_path, 'x') as spec_file:
            spec_file.write(self.kprove.prettyPrint(definition))

        # When
        result = self.kprove.prove(spec_path, spec_module_name)

        # Then
        self.assertEqual(result['label'], '#Top')


def extract_claims(module):
    return [claim for claim in module['localSentences'] if claim['node'] == 'KClaim']


def eliminate_generated_top(term):
    rule = KApply('<generatedTop>', [KVariable('CONFIG'), KVariable('_')]), KVariable('CONFIG')
    return rewriteAnywhereWith(rule, term)
