from unittest import TestCase

from kup import __version__


class VersionTest(TestCase):
    def test_version(self) -> None:
        self.assertEqual(__version__, '0.1.0')
