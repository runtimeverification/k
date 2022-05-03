from abc import ABC

from ..kast import KAs, KDefinition, KSort, KSortSynonym, readKastTerm
from ..ktool import KompileBackend
from .kompiled_test import KompiledTest


class ParseKAstTest(KompiledTest, ABC):
    COMPILED_JSON_PATH: str
    MODULE_NAME: str

    def setUp(self):
        super().setUp()
        self.definition = readKastTerm(self.COMPILED_JSON_PATH)
        self.assertIsInstance(self.definition, KDefinition)
        modules = [module for module in self.definition if module.name == self.MODULE_NAME]
        self.assertEqual(len(modules), 1)
        self.module = modules[0]


class KSortSynonymTest(ParseKAstTest):
    KOMPILE_MAIN_FILE = 'k-files/sort-synonym.k'
    KOMPILE_BACKEND = KompileBackend.HASKELL
    KOMPILE_OUTPUT_DIR = 'definitions/sort-synonym'
    KOMPILE_EMIT_JSON = True

    COMPILED_JSON_PATH = 'definitions/sort-synonym/compiled.json'
    MODULE_NAME = 'SORT-SYNONYM-SYNTAX'

    def test(self):
        sort_synonym = [sentence for sentence in self.module if type(sentence) is KSortSynonym][0]
        self.assertEqual(sort_synonym.new_sort, KSort('NewInt'))
        self.assertEqual(sort_synonym.old_sort, KSort('Int'))


class KAsTest(ParseKAstTest):
    KOMPILE_MAIN_FILE = 'k-files/contextual-function.k'
    KOMPILE_BACKEND = KompileBackend.HASKELL
    KOMPILE_OUTPUT_DIR = 'definitions/contextual-function'
    KOMPILE_EMIT_JSON = True

    COMPILED_JSON_PATH = 'definitions/contextual-function/compiled.json'
    MODULE_NAME = 'CONTEXTUAL-FUNCTION'

    def test(self):
        rule = [sentence for sentence in self.module if sentence.att.get('label') == 'def-get-ctx'][0]
        rewrite = rule.body
        lhs = rewrite.lhs
        kas = lhs.args[0]
        self.assertIsInstance(kas, KAs)
