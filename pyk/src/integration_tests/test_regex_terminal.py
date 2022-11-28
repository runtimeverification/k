from pyk.kast.outer import KRegexTerminal

from .kompiled_test import KompiledTest


class RegexTerminalTest(KompiledTest):
    KOMPILE_MAIN_FILE = 'k-files/regex-terminal.k'

    def test(self) -> None:
        # Given
        expected = [
            KRegexTerminal('b', '#', '#'),
            KRegexTerminal('b', 'a', '#'),
            KRegexTerminal('b', '#', 'c'),
            KRegexTerminal('b', 'a', 'c'),
        ]

        module = [module for module in self.definition if module.name == 'REGEX-TERMINAL-SYNTAX'][0]
        productions = sorted(
            (
                prod
                for prod in module.productions
                if prod.sort.name in {'T0', 'T1', 'T2', 'T3'} and type(prod.items[0]) is KRegexTerminal
            ),
            key=lambda prod: prod.sort.name,
        )

        actual = [prod.items[0] for prod in productions]

        # Then
        self.assertListEqual(expected, actual)
