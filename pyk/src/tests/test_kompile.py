from pathlib import Path
from unittest import TestCase

from pyk.ktool.kompile import KompileBackend, _build_arg_list


class BuildArgsTest(TestCase):
    def test_all_args(self) -> None:
        actual = _build_arg_list(
            main_module='MAIN-MODULE',
            syntax_module='SYNTAX-MODULE',
            backend=KompileBackend.HASKELL,
            output_dir=Path('path/to/kompiled'),
            include_dirs=(Path(path) for path in ['/', '/include/lib']),
            md_selector='k & ! nobytes & ! node',
            hook_namespaces=['JSON', 'KRYPTO', 'BLOCKCHAIN'],
            emit_json=True,
            post_process='echo "hello"',
            concrete_rules=['foo', 'bar'],
            args=['--new-fangled-option', 'buzz'],
        )
        # fmt: off
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
            '--post-process', "'echo \"hello\"'",
            '--concrete-rules', 'foo,bar',
            '--new-fangled-option', 'buzz'
        ]
        # fmt: on
        self.assertEqual(actual, expected)
