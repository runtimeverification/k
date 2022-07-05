from pathlib import Path
from unittest import TestCase

from ..ktool.kompile import KompileBackend, _build_arg_list


class BuildArgsTest(TestCase):
    def test_all_args(self):
        actual = _build_arg_list(
            main_module='MAIN-MODULE',
            syntax_module='SYNTAX-MODULE',
            backend=KompileBackend.HASKELL,
            output_dir=Path('path/to/kompiled'),
            include_dirs=['/', '/include/lib'],
            md_selector='k & ! nobytes & ! node',
            hook_namespaces=['JSON', 'KRYPTO', 'BLOCKCHAIN'],
            emit_json=True,
            concrete_rules=['foo', 'bar'],
            additional_args=['--new-fangled-option', 'buzz']
        )
        expected = [
            '--main-module', 'MAIN-MODULE',
            '--syntax-module', 'SYNTAX-MODULE',
            '--backend', 'haskell',
            '--output-definition', 'path/to/kompiled',
            '-I', '/',
            '-I', '/include/lib',
            '--md-selector', 'k & ! nobytes & ! node',
            '--hook-namespaces', 'JSON KRYPTO BLOCKCHAIN',
            '--emit-json',
            '--concrete-rules', 'foo,bar',
            '--new-fangled-option', 'buzz'
        ]
        self.assertEqual(actual, expected)
