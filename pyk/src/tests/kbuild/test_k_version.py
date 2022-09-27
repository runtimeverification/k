from unittest import TestCase

from pyk.kbuild.utils import KVersion


class KVersionTest(TestCase):
    def test_parse_valid(self) -> None:
        # Given
        test_data = (
            ('5.4.7', KVersion(5, 4, 7, None)),
            ('v5.4.7-0-g0b0189cc60', KVersion(5, 4, 7, KVersion.Git(0, '0b0189cc60', False))),
            ('v5.4.7-0-g0b0189cc60-dirty', KVersion(5, 4, 7, KVersion.Git(0, '0b0189cc60', True))),
        )

        for version, expected in test_data:
            with self.subTest(version):
                # When
                actual = KVersion.parse(version)

                # Then
                self.assertEqual(actual, expected)
                self.assertEqual(actual.text, version)

    def test_parse_invalid(self) -> None:
        # Given
        test_data = (
            '',
            'a',
            '1',
            '1.2',
            '1.2',
            'v1.2.3',
            '1.2.3-dirty',
            'v1.2.3-10',
            'v1.2.3-10-dirty',
            'v1.2.3-10-0123',
            'v1.2.3-a-0123456789',
            '1.2.3-10-0123456789',
        )

        for version in test_data:
            with self.subTest(version):
                with self.assertRaises(ValueError) as cm:
                    # When
                    KVersion.parse(version)

                # Then
                self.assertEqual(cm.exception.args[0], f'Invalid K version string: {version}')
