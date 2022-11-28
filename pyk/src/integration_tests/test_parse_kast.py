from typing import ClassVar

from pyk.kast.inner import KApply, KAs, KRewrite, KSort
from pyk.kast.outer import KSortSynonym
from pyk.utils import single

from .kompiled_test import KompiledTest


class ParseKAstTest(KompiledTest):
    MODULE_NAME: ClassVar[str]

    def setUp(self) -> None:
        super().setUp()
        self.module = single(module for module in self.definition if module.name == self.MODULE_NAME)


class KSortSynonymTest(ParseKAstTest):
    KOMPILE_MAIN_FILE = 'k-files/sort-synonym.k'

    MODULE_NAME = 'SORT-SYNONYM-SYNTAX'

    def test(self) -> None:
        sort_synonym = [sentence for sentence in self.module if type(sentence) is KSortSynonym][0]
        self.assertEqual(sort_synonym.new_sort, KSort('NewInt'))
        self.assertEqual(sort_synonym.old_sort, KSort('Int'))


class KAsTest(ParseKAstTest):
    KOMPILE_MAIN_FILE = 'k-files/contextual-function.k'

    MODULE_NAME = 'CONTEXTUAL-FUNCTION'

    def test(self) -> None:
        rule = [rule for rule in self.module.rules if rule.att.get('label') == 'def-get-ctx'][0]
        rewrite = rule.body
        assert type(rewrite) is KRewrite
        lhs = rewrite.lhs
        assert type(lhs) is KApply
        kas = lhs.args[0]
        self.assertIsInstance(kas, KAs)
