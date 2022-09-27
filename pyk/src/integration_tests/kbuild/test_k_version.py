from unittest import TestCase

from pyk.kbuild.utils import KVersion, k_version


class KVersionTest(TestCase):
    def test(self) -> None:
        # When
        version1 = k_version()
        version2 = KVersion.parse(version1.text)

        # Then
        self.assertEqual(version1, version2)
