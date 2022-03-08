from abc import ABC
from unittest import TestCase

from pyk.kast import KAs, KDefinition, KRule, KSort, KSortSynonym, readKastTerm


class ParseKAstTest(TestCase, ABC):
    COMPILED_JSON_PATH: str
    MODULE_NAME: str

    def setUp(self):
        self.definition = readKastTerm(self.COMPILED_JSON_PATH)
        self.assertIsInstance(self.definition, KDefinition)
        modules = [module for module in self.definition if module.name == self.MODULE_NAME]
        self.assertEqual(len(modules), 1)
        self.module = modules[0]


class KSortSynonymTest(ParseKAstTest):
    COMPILED_JSON_PATH = 'definitions/sort-synonym/haskell/sort-synonym-kompiled/compiled.json'
    MODULE_NAME = 'SORT-SYNONYM-SYNTAX'

    def test(self):
        sort_synonym = [sentence for sentence in self.module if type(sentence) is KSortSynonym][0]
        self.assertEqual(sort_synonym.new_sort, KSort('NewInt'))
        self.assertEqual(sort_synonym.old_sort, KSort('Int'))


class KAsTest(ParseKAstTest):
    COMPILED_JSON_PATH = 'definitions/contextual-function/haskell/contextual-function-kompiled/compiled.json'
    MODULE_NAME = 'CONTEXTUAL-FUNCTION'

    def test(self):
        rule = [sentence for sentence in self.module if sentence.att.get('label') == 'def-get-ctx'][0]
        rewrite = rule.body
        lhs = rewrite.lhs
        kas = lhs.args[0]
        self.assertIsInstance(kas, KAs)
